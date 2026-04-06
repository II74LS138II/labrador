#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "randombytes.h"
#include "fips202.h"
#include "chihuahua.h"
#include "pack.h"


#include "cJSON.h"
#include "polx.h" // 可能包含在其他头文件中了，如果报错请加上

// 确保这里的参数与你的 Plover 和 LaBRADOR 的设定一致
#define PLOVER_N 256
#define DEG 1  // LaBRADOR 的扩展度，如果是简单多项式，通常为 1 (如果 test 原码是 8 则改为 8)

// --- 辅助函数：读取文件内容 ---
char* read_file_to_string(const char* filename) {
    FILE *f = fopen(filename, "r");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long length = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *data = malloc(length + 1);
    fread(data, 1, length, f);
    fclose(f);
    data[length] = '\0';
    return data;
}

// --- 辅助函数：从 JSON 读取到 int64_t 数组 ---
void load_poly_array(cJSON *array, int64_t *dest, size_t n) {
    int i = 0;
    cJSON *item = NULL;
    cJSON_ArrayForEach(item, array) {
        if (i >= n) break;
        dest[i] = (int64_t)item->valuedouble;
        i++;
    }
}

// === 核心：LaBRADOR 数据装载器 ===
static int prepare_plover_linear(prncplstmnt *st, witness *wt, const char* json_path) {
    char* json_string = read_file_to_string(json_path);
    if (!json_string) {
        printf("无法读取文件 %s\n", json_path);
        return -1;
    }
    
    cJSON *json = cJSON_Parse(json_string);
    cJSON *stmt_json = cJSON_GetObjectItemCaseSensitive(json, "statement");
    cJSON *wit_json  = cJSON_GetObjectItemCaseSensitive(json, "witness");

    uint64_t plover_sq_beta = (uint64_t)cJSON_GetObjectItemCaseSensitive(stmt_json, "sq_beta")->valuedouble;

    // 1. 系统维度定义
    size_t r = 3;  // 3 个见证: z1, z2, c1
    size_t n[3] = {PLOVER_N, PLOVER_N, PLOVER_N};
    size_t idx[3] = {0, 1, 2}; // 约束矩阵涉及的列索引

    // 2. 初始化 Witness 结构
    init_witness_raw(wt, r, n);

    // --- 3. 填充隐私见证 (Witness) ---
    int64_t raw_z1[PLOVER_N] = {0};
    int64_t raw_z2[PLOVER_N] = {0};
    int64_t raw_c1[PLOVER_N] = {0};

    load_poly_array(cJSON_GetObjectItemCaseSensitive(wit_json, "z1"), raw_z1, PLOVER_N);
    load_poly_array(cJSON_GetObjectItemCaseSensitive(wit_json, "z2"), raw_z2, PLOVER_N);
    load_poly_array(cJSON_GetObjectItemCaseSensitive(wit_json, "c1"), raw_c1, PLOVER_N);

    // 将普通数组转换为 LaBRADOR 内部的多项式格式
    // （如果底层 wt->s 是 polz 类型，请使用 polzvec_fromint64vec）
    polxvec_fromint64vec(wt->s[0], 1, DEG, raw_z1);
    polxvec_fromint64vec(wt->s[1], 1, DEG, raw_z2);
    polxvec_fromint64vec(wt->s[2], 1, DEG, raw_c1);

    // --- 4. 初始化并填充公开声明 ---
    init_prncplstmnt_raw(st, r, n, plover_sq_beta, 1, 0); // 1 代表 1 个约束方程

    // 构造方程：1*z1 + A*z2 + t*c1 = u
    // 展平为一维数组，长度为 3 * PLOVER_N
    int64_t *phi_raw = calloc(3 * PLOVER_N, sizeof(int64_t)); 
    int64_t b_raw[PLOVER_N] = {0};

    // a) Phi 第 1 段：对应 z1，系数是常数 1
    phi_raw[0] = 1; 

    // b) Phi 第 2 段：对应 z2，系数是 A
    load_poly_array(cJSON_GetObjectItemCaseSensitive(stmt_json, "A"), &phi_raw[PLOVER_N], PLOVER_N);

    // c) Phi 第 3 段：对应 c1，系数是 t
    load_poly_array(cJSON_GetObjectItemCaseSensitive(stmt_json, "t"), &phi_raw[2 * PLOVER_N], PLOVER_N);

    // d) 等式右侧目标值：对应 u
    load_poly_array(cJSON_GetObjectItemCaseSensitive(stmt_json, "u"), b_raw, PLOVER_N);

    // 调用接口直接注入
    set_prncplstmnt_lincnst_raw(st, 0, 3, idx, n, DEG, phi_raw, b_raw);

    // 5. 资源释放与返回
    free(phi_raw);
    cJSON_Delete(json);
    free(json_string);
    
    printf("\n[+] 成功：PloverSign 的数据已完美装载到 LaBRADOR 电路中！\n");
    return 0;
}

static void prepare_linear(prncplstmnt *st, witness *wt) {
  size_t i,j,l;
  __attribute__((aligned(16)))
  uint8_t seed[16];
  uint64_t nonce = 0;
  shake128incctx shakectx;
  sparsecnst *cnst;
  polx *buf;

  size_t r = 1;
  size_t n[r];
  for(i=0;i<r;i++)
    n[i] = 1<<11;
  size_t k = 2;
  size_t deg = 8;
  size_t deg2 = 8; // next2power
  size_t betasq = 0;
  for(i=0;i<r;i++)
    betasq += 1.15*10/16*n[i]*N;

  __attribute__((aligned(16)))
  uint8_t hashbuf[deg2*N*QBYTES];
  polx *sx[r];
  polz t[deg2];

  randombytes(seed,sizeof(seed));
  init_witness_raw(wt,r,n);
  for(i=0;i<r;i++) {
    polyvec_ternary(wt->s[i],wt->n[i],seed,nonce++);
    wt->normsq[i] = polyvec_sprodz(wt->s[i],wt->s[i],wt->n[i]);
  }

  *sx = NULL;
  shake128_inc_init(&shakectx);
  init_prncplstmnt_raw(st,r,n,betasq,k,0);
  for(i=0;i<k;i++) {
    cnst = &st->cnst[i];
    l = extlen(n[0],deg);
    buf = init_sparsecnst_half(cnst,r,1,l,deg,0,0);

    cnst->idx[0] = 0;
    cnst->off[0] = 0;
    cnst->len[0] = n[0];
    cnst->mult[0] = 1;
    cnst->phi[0] = buf;

    for(j=0;j<l;j+=deg2) {
      polzvec_almostuniform(t,deg2,seed,nonce++);
      polzvec_bitpack(hashbuf,t,deg2);
      shake128_inc_absorb(&shakectx,hashbuf,deg2*N*QBYTES);
      polzvec_topolxvec(&cnst->phi[0][j],t,deg2);
    }

    sparsecnst_eval(cnst->b,cnst,sx,wt);
    polzvec_frompolxvec(t,cnst->b,deg);
    polzvec_bitpack(hashbuf,t,deg);
    shake128_inc_absorb(&shakectx,hashbuf,deg*N*QBYTES);
  }

  free(*sx);
  shake128_inc_finalize(&shakectx);
  shake128_inc_squeeze(st->h,16,&shakectx);
}

static int test_twolayer() {
  int ret;
  prncplstmnt st0 = {};
  statement st1 = {}, st2 = {};
  proof pi0 = {}, pi1 = {};
  witness wt0 = {}, wt1 = {}, wt2 = {};
  double size = 0;

  printf("Testing Chihuahua followed by one Labrador\n\n");

  prepare_linear(&st0,&wt0);
  print_prncplstmnt_pp(&st0);
  ret = principle_verify(&st0,&wt0);
  if(ret) {
    fprintf(stderr,"ERROR: Verification of prepare_linear failed: %d\n",ret);
    goto end;
  }

  ret = principle_prove(&st1,&wt1,&pi0,&st0,&wt0,0);
  if(ret) {
    fprintf(stderr,"ERROR: Chihuahua proof failed: %d\n",ret);
    goto end;
  }
  free_witness(&wt0);
  size += print_proof_pp(&pi0);
  print_statement_pp(&st1);
  ret = verify(&st1,&wt1);
  if(ret) {
    fprintf(stderr,"ERROR: Chihuahua verification failed: %d\n",ret);
    goto end;
  }

  free_statement(&st1);
  ret = principle_reduce(&st1,&pi0,&st0);
  free_prncplstmnt(&st0);
  if(ret) {
    fprintf(stderr,"ERROR: Chihuahua reduction failed: %d\n",ret);
    goto end;
  }
  ret = verify(&st1,&wt1);
  if(ret) {
    fprintf(stderr,"ERROR: Verification of chihuahua reduction failed: %d\n",ret);
    goto end;
  }

  ret = prove(&st2,&wt2,&pi1,&st1,&wt1,0);
  if(ret) {
    fprintf(stderr,"ERROR: Labrador proof failed: %d\n",ret);
    goto end;
  }
  free_witness(&wt1);
  size += print_proof_pp(&pi1);
  print_statement_pp(&st2);
  ret = verify(&st2,&wt2);
  if(ret) {
    fprintf(stderr,"ERROR: Labrador verification failed: %d\n",ret);
    goto end;
  }

  free_statement(&st2);
  ret = reduce(&st2,&pi1,&st1);
  free_statement(&st1);
  if(ret) {
    fprintf(stderr,"ERROR: Labrador reduction failed: %d\n",ret);
    goto end;
  }
  ret = verify(&st2,&wt2);
  if(ret) {
    fprintf(stderr,"ERROR: Verification of Labrador reduction failed: %d\n",ret);
    goto end;
  }

  size += print_witness_pp(&wt2);
  printf("Total proof size: %.2f KB\n",size);
  printf("\n");

end:
  free_prncplstmnt(&st0);
  free_statement(&st1);
  free_statement(&st2);
  free_proof(&pi0);
  free_proof(&pi1);
  free_witness(&wt0);
  free_witness(&wt1);
  free_witness(&wt2);
  return ret;
}

static int test_pack() {
  int ret;
  prncplstmnt st = {};
  witness wt = {};
  composite p = {};

  printf("Testing Chihuahua Composite\n\n");

  // prepare_linear(&st,&wt);
  if (prepare_plover_linear(&st, &wt, "plover_labrador.json") != 0) {
    printf("装载失败退出\n");
    return -1;
  }
  print_prncplstmnt_pp(&st);
  ret = principle_verify(&st,&wt);
  if(ret) {
    fprintf(stderr,"ERROR: Verification of prepare_linear failed: %d\n",ret);
    goto end;
  }

  ret = composite_prove_principle(&p,&st,&wt);
  if(ret) {
    fprintf(stderr,"ERROR: Chihuahua composite proof failed: %d\n",ret);
    goto end;
  }
  ret = composite_verify_principle(&p,&st);
  if(ret) {
    fprintf(stderr,"ERROR: Chihuahua composite verifaction failed: %d\n",ret);
    goto end;
  }

end:
  free_prncplstmnt(&st);
  free_composite(&p);
  free_witness(&wt);
  return ret;
}

int main(void) {
  int ret;

  ret = test_twolayer();
  if(ret) goto end;
  ret = test_pack();
  if(ret) goto end;

end:
  free_comkey();
  return ret;
}
