#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Comparison {
  enum class cmp { CmpLt, CmpEq, CmpGt };

  template <typename T1>
  static T1 cmp_rect(const T1 f, const T1 f0, const T1 f1, const cmp c) {
    return [&](void) {
      switch (c) {
      case cmp::CmpLt: {
        return f;
      }
      case cmp::CmpEq: {
        return f0;
      }
      case cmp::CmpGt: {
        return f1;
      }
      }
    }();
  }

  template <typename T1>
  static T1 cmp_rec(const T1 f, const T1 f0, const T1 f1, const cmp c) {
    return [&](void) {
      switch (c) {
      case cmp::CmpLt: {
        return f;
      }
      case cmp::CmpEq: {
        return f0;
      }
      case cmp::CmpGt: {
        return f1;
      }
      }
    }();
  }

  static unsigned int cmp_to_nat(const cmp c);

  static cmp compare_nats(const unsigned int a, const unsigned int b);

  static unsigned int max_nat(const unsigned int a, const unsigned int b);

  static unsigned int min_nat(const unsigned int a, const unsigned int b);

  static unsigned int clamp(const unsigned int val0, const unsigned int lo,
                            const unsigned int hi);

  static cmp flip_cmp(const cmp c);

  static inline const unsigned int test_lt_nat = cmp_to_nat(cmp::CmpLt);

  static inline const unsigned int test_eq_nat = cmp_to_nat(cmp::CmpEq);

  static inline const unsigned int test_gt_nat = cmp_to_nat(cmp::CmpGt);

  static inline const cmp test_compare_lt = compare_nats(3u, 5u);

  static inline const cmp test_compare_eq = compare_nats(5u, 5u);

  static inline const cmp test_compare_gt = compare_nats(7u, 5u);

  static inline const unsigned int test_max = max_nat(3u, 7u);

  static inline const unsigned int test_min = min_nat(3u, 7u);

  static inline const unsigned int test_clamp_lo = clamp(1u, 3u, 7u);

  static inline const unsigned int test_clamp_mid = clamp(5u, 3u, 7u);

  static inline const unsigned int test_clamp_hi = clamp(9u, 3u, 7u);

  static inline const cmp test_flip = flip_cmp(cmp::CmpLt);
};
