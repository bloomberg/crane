#ifndef INCLUDED_EXISTENTIAL_CLOSURE_PROBE
#define INCLUDED_EXISTENTIAL_CLOSURE_PROBE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <cstdint>
#include <utility>
#include <variant>

struct ExistentialClosureProbe {
  /// Type-indexed inductive wrapping a value of erased type.
  /// The type index A is erased to std::any by Crane.
  /// Values stored in the wrapper must be recovered via any_cast.
  struct wrap {
    // DATA
    crane::obj a;

    // ACCESSORS
    wrap clone() const { return {a}; }

    // CREATORS
    static wrap wrap0(crane::obj a) { return {std::move(a)}; }
  };

  template <typename T1, typename T2 = void, typename F0>
  static T1 wrap_rect(F0 &&f, const wrap &w) {
    const auto &[a0] = w;
    return crane_any_cast<T1>(crane_call_erased(f, crane_any_cast<T2>(a0)));
  }

  template <typename T1, typename T2 = void, typename F0>
  static T1 wrap_rec(F0 &&f, const wrap &w) {
    return wrap_rect<T1, crane::obj>(crane_erase_fn<T1>(f), w);
  }

  template <typename T1> static T1 unwrap(const wrap &w) {
    const auto &[a] = w;
    return crane_any_cast<T1>(a);
  }

  /// Pack a closure into a type-erased wrapper.
  static wrap pack_fn(uint64_t base);
  /// Unpack and apply.
  static uint64_t apply_packed(const wrap &x0_, uint64_t x1_);
  /// test1: pack base=10, apply to 5. Expected: 15.
  static constexpr uint64_t test1 = UINT64_C(15);
  /// test2: Pack and unpack through a let binding.
  /// base=42, apply to 0. Expected: 42.
  static constexpr uint64_t test2 = UINT64_C(42);
  /// Store a closure that captures another closure.
  static wrap pack_composed(uint64_t a, uint64_t b);
  /// test3: a=3, b=2, g(5) = (5+3)*2 = 16.
  static constexpr uint64_t test3 = UINT64_C(16);
};

#endif // INCLUDED_EXISTENTIAL_CLOSURE_PROBE
