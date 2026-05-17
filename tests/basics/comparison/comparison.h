#ifndef INCLUDED_COMPARISON
#define INCLUDED_COMPARISON

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

  static unsigned int cmp_to_nat(Cmp c);
  static Cmp compare_nats(unsigned int a, unsigned int b);
  static unsigned int max_nat(unsigned int a, unsigned int b);
  static unsigned int min_nat(unsigned int a, unsigned int b);
  static unsigned int clamp(unsigned int val, unsigned int lo, unsigned int hi);
  static Cmp flip_cmp(Cmp c);
  static inline const unsigned int test_lt_nat = cmp_to_nat(Cmp::CMPLT);
  static inline const unsigned int test_eq_nat = cmp_to_nat(Cmp::CMPEQ);
  static inline const unsigned int test_gt_nat = cmp_to_nat(Cmp::CMPGT);
  static inline const Cmp test_compare_lt = compare_nats(3u, 5u);
  static inline const Cmp test_compare_eq = compare_nats(5u, 5u);
  static inline const Cmp test_compare_gt = compare_nats(7u, 5u);
  static inline const unsigned int test_max = max_nat(3u, 7u);
  static inline const unsigned int test_min = min_nat(3u, 7u);
  static inline const unsigned int test_clamp_lo = clamp(1u, 3u, 7u);
  static inline const unsigned int test_clamp_mid = clamp(5u, 3u, 7u);
  static inline const unsigned int test_clamp_hi = clamp(9u, 3u, 7u);
  static inline const Cmp test_flip = flip_cmp(Cmp::CMPLT);
};

#endif // INCLUDED_COMPARISON
