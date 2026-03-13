#ifndef INCLUDED_COMPARISON
#define INCLUDED_COMPARISON

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Comparison {
  enum class Cmp { e_CMPLT, e_CMPEQ, e_CMPGT };

  template <typename T1>
  static T1 cmp_rect(const T1 f, const T1 f0, const T1 f1, const Cmp c) {
    return [&](void) {
      switch (c) {
      case Cmp::e_CMPLT: {
        return f;
      }
      case Cmp::e_CMPEQ: {
        return f0;
      }
      case Cmp::e_CMPGT: {
        return f1;
      }
      }
    }();
  }

  template <typename T1>
  static T1 cmp_rec(const T1 f, const T1 f0, const T1 f1, const Cmp c) {
    return [&](void) {
      switch (c) {
      case Cmp::e_CMPLT: {
        return f;
      }
      case Cmp::e_CMPEQ: {
        return f0;
      }
      case Cmp::e_CMPGT: {
        return f1;
      }
      }
    }();
  }

  __attribute__((pure)) static unsigned int cmp_to_nat(const Cmp c);
  __attribute__((pure)) static Cmp compare_nats(const unsigned int a,
                                                const unsigned int b);
  __attribute__((pure)) static unsigned int max_nat(const unsigned int a,
                                                    const unsigned int b);
  __attribute__((pure)) static unsigned int min_nat(const unsigned int a,
                                                    const unsigned int b);
  __attribute__((pure)) static unsigned int
  clamp(const unsigned int val, const unsigned int lo, const unsigned int hi);
  __attribute__((pure)) static Cmp flip_cmp(const Cmp c);
  static inline const unsigned int test_lt_nat = cmp_to_nat(Cmp::e_CMPLT);
  static inline const unsigned int test_eq_nat = cmp_to_nat(Cmp::e_CMPEQ);
  static inline const unsigned int test_gt_nat = cmp_to_nat(Cmp::e_CMPGT);
  static inline const Cmp test_compare_lt = compare_nats(3u, 5u);
  static inline const Cmp test_compare_eq = compare_nats(5u, 5u);
  static inline const Cmp test_compare_gt = compare_nats(7u, 5u);
  static inline const unsigned int test_max = max_nat(3u, 7u);
  static inline const unsigned int test_min = min_nat(3u, 7u);
  static inline const unsigned int test_clamp_lo = clamp(1u, 3u, 7u);
  static inline const unsigned int test_clamp_mid = clamp(5u, 3u, 7u);
  static inline const unsigned int test_clamp_hi = clamp(9u, 3u, 7u);
  static inline const Cmp test_flip = flip_cmp(Cmp::e_CMPLT);
};

#endif // INCLUDED_COMPARISON
