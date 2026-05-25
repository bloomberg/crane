#ifndef INCLUDED_COMPARISON
#define INCLUDED_COMPARISON

#include <utility>

struct Comparison {
  enum class Cmp { CMPLT, CMPEQ, CMPGT };

  template <typename T1> static T1 cmp_rect(T1 f, T1 f0, T1 f1, Cmp c) {
    switch (c) {
    case Cmp::CMPLT: {
      return f;
    } break;
    case Cmp::CMPEQ: {
      return f0;
    } break;
    case Cmp::CMPGT: {
      return f1;
    } break;
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 cmp_rec(T1 f, T1 f0, T1 f1, Cmp c) {
    switch (c) {
    case Cmp::CMPLT: {
      return f;
    } break;
    case Cmp::CMPEQ: {
      return f0;
    } break;
    case Cmp::CMPGT: {
      return f1;
    } break;
    default:
      std::unreachable();
    }
  }

  static uint64_t cmp_to_nat(Cmp c);
  static Cmp compare_nats(uint64_t a, uint64_t b);
  static uint64_t max_nat(uint64_t a, uint64_t b);
  static uint64_t min_nat(uint64_t a, uint64_t b);
  static uint64_t clamp(uint64_t val, uint64_t lo, uint64_t hi);
  static Cmp flip_cmp(Cmp c);
  static inline const uint64_t test_lt_nat = cmp_to_nat(Cmp::CMPLT);
  static inline const uint64_t test_eq_nat = cmp_to_nat(Cmp::CMPEQ);
  static inline const uint64_t test_gt_nat = cmp_to_nat(Cmp::CMPGT);
  static inline const Cmp test_compare_lt =
      compare_nats(UINT64_C(3), UINT64_C(5));
  static inline const Cmp test_compare_eq =
      compare_nats(UINT64_C(5), UINT64_C(5));
  static inline const Cmp test_compare_gt =
      compare_nats(UINT64_C(7), UINT64_C(5));
  static inline const uint64_t test_max = max_nat(UINT64_C(3), UINT64_C(7));
  static inline const uint64_t test_min = min_nat(UINT64_C(3), UINT64_C(7));
  static inline const uint64_t test_clamp_lo =
      clamp(UINT64_C(1), UINT64_C(3), UINT64_C(7));
  static inline const uint64_t test_clamp_mid =
      clamp(UINT64_C(5), UINT64_C(3), UINT64_C(7));
  static inline const uint64_t test_clamp_hi =
      clamp(UINT64_C(9), UINT64_C(3), UINT64_C(7));
  static inline const Cmp test_flip = flip_cmp(Cmp::CMPLT);
};

#endif // INCLUDED_COMPARISON
