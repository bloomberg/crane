#ifndef INCLUDED_EXISTENTIAL_CLOSURE_PROBE
#define INCLUDED_EXISTENTIAL_CLOSURE_PROBE

#include <any>
#include <functional>
#include <utility>
#include <variant>

struct ExistentialClosureProbe {
  /// Type-indexed inductive wrapping a value of erased type.
  /// The type index A is erased to std::any by Crane.
  /// Values stored in the wrapper must be recovered via any_cast.
  struct wrap {
    // DATA
    std::any a;

    // ACCESSORS
    wrap clone() const { return {a}; }

    // CREATORS
    static wrap wrap0(std::any a) { return {std::move(a)}; }
  };

  template <typename T1, typename T2, typename F0>
  static T1 wrap_rect(F0 &&f, const wrap &w) {
    const auto &[a0] = w;
    return std::any_cast<T1>(f(std::any_cast<T2>(a0)));
  }

  template <typename T1, typename T2, typename F0>
  static T1 wrap_rec(F0 &&f, const wrap &w) {
    const auto &[a0] = w;
    return std::any_cast<T1>(f(std::any_cast<T2>(a0)));
  }

  template <typename T1> static T1 unwrap(const wrap &w) {
    const auto &[a] = w;
    return std::any_cast<T1>(std::any_cast<T1>(a));
  }

  /// Pack a closure into a type-erased wrapper.
  static wrap pack_fn(uint64_t base);
  /// Unpack and apply.
  static uint64_t apply_packed(const wrap &_x0, uint64_t _x1);
  /// test1: pack base=10, apply to 5. Expected: 15.
  static inline const uint64_t test1 =
      apply_packed(pack_fn(UINT64_C(10)), UINT64_C(5));
  /// test2: Pack and unpack through a let binding.
  /// base=42, apply to 0. Expected: 42.
  static inline const uint64_t test2 = []() {
    wrap p = pack_fn(UINT64_C(42));
    return apply_packed(std::move(p), UINT64_C(0));
  }();
  /// Store a closure that captures another closure.
  static wrap pack_composed(uint64_t a, uint64_t b);
  /// test3: a=3, b=2, g(5) = (5+3)*2 = 16.
  static inline const uint64_t test3 =
      apply_packed(pack_composed(UINT64_C(3), UINT64_C(2)), UINT64_C(5));
};

#endif // INCLUDED_EXISTENTIAL_CLOSURE_PROBE
