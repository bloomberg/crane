#ifndef INCLUDED_PROP_ERASURE
#define INCLUDED_PROP_ERASURE

struct PropErasure {
  static uint64_t with_proof_arg(uint64_t n);
  static inline const uint64_t use_proof = with_proof_arg(UINT64_C(5));
  static inline const uint64_t simple_value = UINT64_C(7);
  static uint64_t add_with_proof(uint64_t _x0, uint64_t _x1);
  static inline const uint64_t test_add_proof =
      add_with_proof(UINT64_C(3), UINT64_C(4));
  static inline const uint64_t test_use_proof = use_proof;
  static inline const uint64_t test_simple = simple_value;
};

#endif // INCLUDED_PROP_ERASURE
