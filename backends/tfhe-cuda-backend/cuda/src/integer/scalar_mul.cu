#include "integer/scalar_mul.cuh"

uint64_t scratch_cuda_integer_scalar_mul_kb_64(
    void *const *streams, uint32_t const *gpu_indexes, uint32_t gpu_count,
    int8_t **mem_ptr, uint32_t glwe_dimension, uint32_t polynomial_size,
    uint32_t lwe_dimension, uint32_t ks_level, uint32_t ks_base_log,
    uint32_t pbs_level, uint32_t pbs_base_log, uint32_t grouping_factor,
    uint32_t num_blocks, uint32_t message_modulus, uint32_t carry_modulus,
    PBS_TYPE pbs_type, uint32_t num_scalar_bits, bool allocate_gpu_memory,
    bool allocate_ms_array) {

  int_radix_params params(pbs_type, glwe_dimension, polynomial_size,
                          glwe_dimension * polynomial_size, lwe_dimension,
                          ks_level, ks_base_log, pbs_level, pbs_base_log,
                          grouping_factor, message_modulus, carry_modulus,
                          allocate_ms_array);

  return scratch_cuda_integer_radix_scalar_mul_kb<uint64_t>(
      (cudaStream_t *)(streams), gpu_indexes, gpu_count,
      (int_scalar_mul_buffer<uint64_t> **)mem_ptr, num_blocks, params,
      num_scalar_bits, allocate_gpu_memory);
}

uint64_t scratch_cuda_integer_radix_scalar_mul_high_kb_64(
    void *const *streams, uint32_t const *gpu_indexes, uint32_t gpu_count,
    int8_t **mem_ptr, uint32_t glwe_dimension, uint32_t polynomial_size,
    uint32_t lwe_dimension, uint32_t ks_level, uint32_t ks_base_log,
    uint32_t pbs_level, uint32_t pbs_base_log, uint32_t grouping_factor,
    uint32_t num_blocks, uint32_t message_modulus, uint32_t carry_modulus,
    PBS_TYPE pbs_type, uint32_t num_scalar_bits, bool anticipated_buffer_drop,
    bool allocate_gpu_memory, bool allocate_ms_array) {

  int_radix_params params(pbs_type, glwe_dimension, polynomial_size,
                          glwe_dimension * polynomial_size, lwe_dimension,
                          ks_level, ks_base_log, pbs_level, pbs_base_log,
                          grouping_factor, message_modulus, carry_modulus,
                          allocate_ms_array);

  return scratch_cuda_integer_radix_scalar_mul_high_kb<uint64_t>(
      (cudaStream_t *)(streams), gpu_indexes, gpu_count,
      (int_scalar_mul_high<uint64_t> **)mem_ptr, num_blocks, params,
      num_scalar_bits, anticipated_buffer_drop, allocate_gpu_memory);
}

void cuda_scalar_multiplication_integer_radix_ciphertext_64_inplace(
    void *const *streams, uint32_t const *gpu_indexes, uint32_t gpu_count,
    CudaRadixCiphertextFFI *lwe_array, uint64_t const *decomposed_scalar,
    uint64_t const *has_at_least_one_set, int8_t *mem, void *const *bsks,
    void *const *ksks,
    CudaModulusSwitchNoiseReductionKeyFFI const *ms_noise_reduction_key,
    uint32_t polynomial_size, uint32_t message_modulus, uint32_t num_scalars) {

  switch (polynomial_size) {
  case 512:
    host_integer_scalar_mul_radix<uint64_t, AmortizedDegree<512>>(
        (cudaStream_t *)(streams), gpu_indexes, gpu_count, lwe_array,
        decomposed_scalar, has_at_least_one_set,
        reinterpret_cast<int_scalar_mul_buffer<uint64_t> *>(mem), bsks,
        (uint64_t **)(ksks), ms_noise_reduction_key, message_modulus,
        num_scalars);
    break;
  case 1024:
    host_integer_scalar_mul_radix<uint64_t, AmortizedDegree<1024>>(
        (cudaStream_t *)(streams), gpu_indexes, gpu_count, lwe_array,
        decomposed_scalar, has_at_least_one_set,
        reinterpret_cast<int_scalar_mul_buffer<uint64_t> *>(mem), bsks,
        (uint64_t **)(ksks), ms_noise_reduction_key, message_modulus,
        num_scalars);
    break;
  case 2048:
    host_integer_scalar_mul_radix<uint64_t, AmortizedDegree<2048>>(
        (cudaStream_t *)(streams), gpu_indexes, gpu_count, lwe_array,
        decomposed_scalar, has_at_least_one_set,
        reinterpret_cast<int_scalar_mul_buffer<uint64_t> *>(mem), bsks,
        (uint64_t **)(ksks), ms_noise_reduction_key, message_modulus,
        num_scalars);
    break;
  case 4096:
    host_integer_scalar_mul_radix<uint64_t, AmortizedDegree<4096>>(
        (cudaStream_t *)(streams), gpu_indexes, gpu_count, lwe_array,
        decomposed_scalar, has_at_least_one_set,
        reinterpret_cast<int_scalar_mul_buffer<uint64_t> *>(mem), bsks,
        (uint64_t **)(ksks), ms_noise_reduction_key, message_modulus,
        num_scalars);
    break;
  case 8192:
    host_integer_scalar_mul_radix<uint64_t, AmortizedDegree<8192>>(
        (cudaStream_t *)(streams), gpu_indexes, gpu_count, lwe_array,
        decomposed_scalar, has_at_least_one_set,
        reinterpret_cast<int_scalar_mul_buffer<uint64_t> *>(mem), bsks,
        (uint64_t **)(ksks), ms_noise_reduction_key, message_modulus,
        num_scalars);
    break;
  case 16384:
    host_integer_scalar_mul_radix<uint64_t, AmortizedDegree<16384>>(
        (cudaStream_t *)(streams), gpu_indexes, gpu_count, lwe_array,
        decomposed_scalar, has_at_least_one_set,
        reinterpret_cast<int_scalar_mul_buffer<uint64_t> *>(mem), bsks,
        (uint64_t **)(ksks), ms_noise_reduction_key, message_modulus,
        num_scalars);
    break;
  default:
    PANIC("Cuda error (scalar multiplication): unsupported polynomial size. "
          "Only N = 512, 1024, 2048, 4096, 8192, 16384 are supported.")
  }
}

void cuda_integer_radix_scalar_mul_high_kb_64(
    void *const *streams, uint32_t const *gpu_indexes, uint32_t gpu_count,
    CudaRadixCiphertextFFI *ct, int8_t *mem_ptr, void *const *ksks,
    uint64_t rhs, uint64_t const *decomposed_scalar,
    uint64_t const *has_at_least_one_set,
    CudaModulusSwitchNoiseReductionKeyFFI const *ms_noise_reduction_key,
    void *const *bsks, uint32_t num_scalars) {

  host_integer_radix_scalar_mul_high_kb<uint64_t>(
      (cudaStream_t *)(streams), gpu_indexes, gpu_count, ct,
      (int_scalar_mul_high<uint64_t> *)mem_ptr, (uint64_t **)ksks, rhs,
      decomposed_scalar, has_at_least_one_set, ms_noise_reduction_key, bsks,
      num_scalars);
}

void cleanup_cuda_integer_radix_scalar_mul(void *const *streams,
                                           uint32_t const *gpu_indexes,
                                           uint32_t gpu_count,
                                           int8_t **mem_ptr_void) {

  int_scalar_mul_buffer<uint64_t> *mem_ptr =
      (int_scalar_mul_buffer<uint64_t> *)(*mem_ptr_void);

  mem_ptr->release((cudaStream_t *)(streams), gpu_indexes, gpu_count);
}

void cleanup_cuda_integer_radix_scalar_mul_high_kb_64(
    void *const *streams, uint32_t const *gpu_indexes, uint32_t gpu_count,
    int8_t **mem_ptr_void) {

  int_scalar_mul_high<uint64_t> *mem_ptr =
      (int_scalar_mul_high<uint64_t> *)(*mem_ptr_void);

  mem_ptr->release((cudaStream_t *)streams, gpu_indexes, gpu_count);
}
