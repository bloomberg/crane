#ifndef INCLUDED_COMPARISON
#define INCLUDED_COMPARISON

#include <cstdint>
#include <utility>

struct Comparison {
  enum class Cmp { CMPLT, CMPEQ, CMPGT };

  template <typename T1> static T1 cmp_rect(T1 f, T1 f0, T1 f1, Cmp c) {
    switch (c) {
    case Cmp::CMPLT: {
      return f;
    }
    case Cmp::CMPEQ: {
      return f0;
    }
    case Cmp::CMPGT: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 cmp_rec(T1 f, T1 f0, T1 f1, Cmp c) {
    switch (c) {
    case Cmp::CMPLT: {
      return f;
    }
    case Cmp::CMPEQ: {
      return f0;
    }
    case Cmp::CMPGT: {
      return f1;
    }
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
  static constexpr uint64_t test_lt_nat = UINT64_C(0);
  static constexpr uint64_t test_eq_nat = UINT64_C(1);
  static constexpr uint64_t test_gt_nat = UINT64_C(2);
  static constexpr Cmp test_compare_lt = Cmp::CMPLT;
  static constexpr Cmp test_compare_eq = Cmp::CMPEQ;
  static constexpr Cmp test_compare_gt = Cmp::CMPGT;
  static constexpr uint64_t test_max = UINT64_C(7);
  static constexpr uint64_t test_min = UINT64_C(3);
  static constexpr uint64_t test_clamp_lo = UINT64_C(3);
  static constexpr uint64_t test_clamp_mid = UINT64_C(5);
  static constexpr uint64_t test_clamp_hi = UINT64_C(7);
  static constexpr Cmp test_flip = Cmp::CMPGT;
};

#endif // INCLUDED_COMPARISON
