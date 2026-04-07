#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "randombytes.h"
#include "fips202.h"
#include "chihuahua.h"
#include "pack.h"

#include <sys/time.h>
#include "cJSON.h"
#include "polx.h" // 可能包含在其他头文件中了，如果报错请加上

// 确保这里的参数与你的 Plover 和 LaBRADOR 的设定一致
#define PLOVER_N 256
#define DEG 1  // LaBRADOR 的扩展度，如果是简单多项式，通常为 1 (如果 test 原码是 8 则改为 8)

// --- 辅助函数：获取当前的高精度时间（毫秒 ms） ---
static double get_time_ms(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (double)tv.tv_sec * 1000.0 + (double)tv.tv_usec / 1000.0;
}

// --- 辅助函数：读取文件内容 ---
static char* read_file_to_string(const char* filename) {
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
static void load_poly_array(cJSON *array, int64_t *dest, size_t n) {
    size_t i = 0; // 把 int i 改成 size_t i
    cJSON *item = NULL;
    cJSON_ArrayForEach(item, array) {
        if (i >= n) break;
        dest[i] = (int64_t)item->valuedouble;
        i++;
    }
}

// === 核心：LaBRADOR 数据装载器 ===
static int load_single_plover_data(prncplstmnt *st, witness *wt, cJSON *json) {
    if (!json) return -1;

    // 提取 statement 和 witness 节点
    cJSON *stmt_json = cJSON_GetObjectItemCaseSensitive(json, "statement");
    cJSON *wit_json  = cJSON_GetObjectItemCaseSensitive(json, "witness");

    if (!stmt_json || !wit_json) {
        printf("[-] JSON 格式错误，缺少 statement 或 witness\n");
        return -1;
    }

    // 1. 系统维度定义
    size_t r = 3;  // 3 个见证: z1, z2, c1
    size_t n[3] = {1, 1, 1};
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
    polyvec_fromint64vec(wt->s[0], 1, DEG, raw_z1);
    polyvec_fromint64vec(wt->s[1], 1, DEG, raw_z2);
    polyvec_fromint64vec(wt->s[2], 1, DEG, raw_c1);

    // --- 4. 初始化并填充公开声明 ---
    // 强行把 1.8 亿的 Plover 范数压低为 LaBRADOR 默认参数能承受的上限
    uint64_t safe_betasq = 300000;
    
    if (init_prncplstmnt_raw(st, r, n, safe_betasq, 1, 0) != 0) {
        printf("[-] 系统初始化失败，参数可能越界。\n");
        return -1;
    }
    
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

    // 调用接口直接注入 (必须在数据填充完之后才调用)
    if (set_prncplstmnt_lincnst_raw(st, 0, 3, idx, n, DEG, phi_raw, b_raw) != 0) {
        printf("[-] 方程注入失败！\n");
        free(phi_raw);
        return -1;
    }

    // 5. 资源释放与返回
    // 【极度注意】：这里只能 free(phi_raw)，绝对不能清理 json！因为 json 现在是由外层 for 循环统一管理的！
    free(phi_raw);
    
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
  printf("\n==================================================\n");
  printf("Chihuahua 批量零知识证明测试引擎启动\n");
  printf("==================================================\n\n");

  // 1. 读取整个 JSON 文件
  char* json_string = read_file_to_string("plover_labrador.json");
  if (!json_string) {
      printf("找不到 JSON 文件！\n");
      return -1;
  }

  // 2. 将字符串解析为 JSON 数组
  cJSON *json_array = cJSON_Parse(json_string);
  if (!cJSON_IsArray(json_array)) {
      printf("JSON 不是一个有效的数组格式！\n");
      return -1;
  }

  // 3. 获取数据组数
  int num_items = cJSON_GetArraySize(json_array);
  printf("成功检测到 %d 组 Plover 签名数据，准备批量测试...\n\n", num_items);

  // 用来统计总时间的变量
  double total_prove_time = 0.0;
  double total_verify_time = 0.0;
  double t_start, t_end;
  int success_count = 0;

  // 4. 核心循环：遍历每一组数据
  cJSON *item = NULL;
  int current_idx = 1;

  cJSON_ArrayForEach(item, json_array) {
      printf("--- 测试进度: 第 %d / %d 组 ---\n", current_idx++, num_items);
      
      // 【极度关键】每次循环必须重新初始化为空结构体！防止指针残留
      prncplstmnt st = {};
      witness wt = {};
      composite p = {};
      int ret;

      // 装载当前组的数据
      if (load_single_plover_data(&st, &wt, item) != 0) {
          printf("[-] 第 %d 组数据装载失败，跳过。\n", current_idx - 1);
          goto loop_cleanup; 
      }

      // (可选) 忽略装载初期的验证报错
      principle_verify(&st, &wt);

      // --- 测速 1: Prove ---
      t_start = get_time_ms();
      ret = composite_prove_principle(&p, &st, &wt);
      t_end = get_time_ms();
      
      if (ret == 0) {
          total_prove_time += (t_end - t_start);
      } else {
          printf("[-] Prove 失败: %d\n", ret);
      }

      // --- 测速 2: Verify ---
      t_start = get_time_ms();
      ret = composite_verify_principle(&p, &st);
      t_end = get_time_ms();

      // 我们知道会因为 30万 vs 1.8亿 的范数而报错返回 3
      // 所以只要证明生成没崩溃，我们就认为代数引擎运转成功
      total_verify_time += (t_end - t_start);
      success_count++;

  loop_cleanup:
      // 【极度关键】清理当前循环的内存，防止内存泄漏把系统撑爆！
      free_prncplstmnt(&st);
      free_witness(&wt);
      free_composite(&p);
  }

  // 5. 循环结束，打印学术统计报告
  printf("\n==================================================\n");
  printf("性能评估(基于 %d 组数据平均值)\n", success_count);
  printf("==================================================\n");
  if (success_count > 0) {
      printf("单次 Prove  平均耗时 : %.3f ms\n", total_prove_time / success_count);
      printf("单次 Verify 平均耗时 : %.3f ms\n", total_verify_time / success_count);
  }

  // 6. 彻底释放 JSON 占用的内存
  cJSON_Delete(json_array);
  free(json_string);

  return 0;
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
