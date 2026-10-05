#ifndef INCLUDED_MEM_SAFETY_PROBE12
#define INCLUDED_MEM_SAFETY_PROBE12

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <cstdint>
#include <utility>
#include <variant>

struct MemSafetyProbe12 {
  /// wrap : Set -> Type is a type-indexed inductive.
  /// ind_nparams = 0, so all field types become std::any.
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
    const auto &[a0] = w;
    return crane_any_cast<T1>(crane_call_erased(f, crane_any_cast<T2>(a0)));
  }

  /// Unwrap extracts the value from wrap A.
  template <typename T1> static T1 unwrap(const wrap &w) {
    const auto &[a0] = w;
    return crane_any_cast<T1>(a0);
  }

  /// TEST 1: Pack a NAT — should work since nat = unsigned int.
  static inline const wrap pack_nat = wrap::wrap0(UINT64_C(42));
  static constexpr uint64_t test_pack_nat = UINT64_C(42);
  /// TEST 2: Pack a BOOL — tests non-function values.
  static inline const wrap pack_bool = wrap::wrap0(true);
  static constexpr bool test_pack_bool = true;
  /// TEST 3: Pack a LET-BOUND closure.
  /// let f := fun x => x + base in Wrap (nat -> nat) f
  /// This should work because f has type std::function<...>
  /// by the time it's passed to Wrap.
  static wrap pack_fn_let(uint64_t base);
  static constexpr uint64_t test_pack_fn_let = UINT64_C(15);
  /// TEST 4: Pack a DIRECT lambda (no let-binding).
  /// Wrap (nat -> nat) (fun x => x + base)
  /// BUG: The raw lambda type is stored in std::any,
  /// but unwrap tries any_cast<std::function<...>>.
  static wrap pack_fn_direct(uint64_t base);
  static constexpr uint64_t test_pack_fn_direct = UINT64_C(15);

  /// TEST 5: Pack a composed closure (let-bound, safe path).
  static wrap pack_composed(crane::fn<uint64_t(uint64_t)> f, uint64_t base) {
    crane::fn<uint64_t(uint64_t)> g = [=](uint64_t x) { return (f(x) + base); };
    return wrap::wrap0(std::move(g));
  }

  static constexpr uint64_t test_pack_composed = UINT64_C(25);
  /// TEST 6: Multiple wraps and unwraps.
  static constexpr uint64_t test_multi_wrap = UINT64_C(30);
  /// TEST 7: Wrap a pair of nats.
  static inline const uint64_t test_wrap_pair = []() {
    std::pair<uint64_t, uint64_t> p = std::make_pair(UINT64_C(3), UINT64_C(7));
    wrap w = wrap::wrap0(std::move(p));
    std::pair<uint64_t, uint64_t> p2 =
        unwrap<std::pair<uint64_t, uint64_t>>(std::move(w));
    return (p2.first + p2.second);
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE12
