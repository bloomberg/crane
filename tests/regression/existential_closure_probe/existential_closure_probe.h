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
    return std::any_cast<T1>(a);
  }

  /// Pack a closure into a type-erased wrapper.
  static wrap pack_fn(unsigned int base);
  /// Unpack and apply.
  static unsigned int apply_packed(const wrap &_x0, unsigned int _x1);
  /// test1: pack base=10, apply to 5. Expected: 15.
  static inline const unsigned int test1 = apply_packed(pack_fn(10u), 5u);
  /// test2: Pack and unpack through a let binding.
  /// base=42, apply to 0. Expected: 42.
  static inline const unsigned int test2 = []() {
    wrap p = pack_fn(42u);
    return apply_packed(std::move(p), 0u);
  }();
  /// Store a closure that captures another closure.
  static wrap pack_composed(unsigned int a, unsigned int b);
  /// test3: a=3, b=2, g(5) = (5+3)*2 = 16.
  static inline const unsigned int test3 =
      apply_packed(pack_composed(3u, 2u), 5u);
};

#endif // INCLUDED_EXISTENTIAL_CLOSURE_PROBE
