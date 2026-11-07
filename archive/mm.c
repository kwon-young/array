__kernel void matrix_multiply(
    __global float* A,
    __global float* B,
    __global float* C,
    int M,
    int K,
    int N) {
  int m = get_global_id(1);
  int n = get_global_id(0);
  
  A += m*K;
  B += n;

  float sum = 0.0f;

  for (int k = 0; k < K; k++) {
    sum += *A * *B;
    A += 1;
    B += N;
  }
  C[m*N+n] = sum;
}
