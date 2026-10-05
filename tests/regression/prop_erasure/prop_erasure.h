#ifndef INCLUDED_PROP_ERASURE
#define INCLUDED_PROP_ERASURE

#include <cstdint>

struct PropErasure {
  static uint64_t with_proof_arg(uint64_t n);
  static constexpr uint64_t use_proof = UINT64_C(5);
  static constexpr uint64_t simple_value = UINT64_C(7);
  static uint64_t add_with_proof(uint64_t x0_, uint64_t x1_);
  static constexpr uint64_t test_add_proof = UINT64_C(7);
  static constexpr uint64_t test_use_proof = UINT64_C(5);
  static constexpr uint64_t test_simple = UINT64_C(7);
};

#endif // INCLUDED_PROP_ERASURE
