#ifndef INCLUDED_MEM_SAFETY_PROBE12
#define INCLUDED_MEM_SAFETY_PROBE12

#include <any>
#include <functional>
#include <type_traits>
#include <utility>
#include <variant>

struct MemSafetyProbe12 {
  /// wrap : Set -> Type is a type-indexed inductive.
  /// ind_nparams = 0, so all field types become std::any.
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

  /// Unwrap extracts the value from wrap A.
  template <typename T1> static T1 unwrap(const wrap &w) {
    const auto &[a0] = w;
    return std::any_cast<T1>(a0);
  }

  /// TEST 1: Pack a NAT — should work since nat = unsigned int.
  static inline const wrap pack_nat = wrap::wrap0(UINT64_C(42));
  static inline const uint64_t test_pack_nat = unwrap<uint64_t>(pack_nat);
  /// TEST 2: Pack a BOOL — tests non-function values.
  static inline const wrap pack_bool = wrap::wrap0(true);
  static inline const bool test_pack_bool = unwrap<bool>(pack_bool);
  /// TEST 3: Pack a LET-BOUND closure.
  /// let f := fun x => x + base in Wrap (nat -> nat) f
  /// This should work because f has type std::function<...>
  /// by the time it's passed to Wrap.
  static wrap pack_fn_let(uint64_t base);
  static inline const uint64_t test_pack_fn_let = []() {
    wrap w = pack_fn_let(UINT64_C(10));
    return unwrap<std::function<uint64_t(uint64_t)>>(std::move(w))(UINT64_C(5));
  }();
  /// TEST 4: Pack a DIRECT lambda (no let-binding).
  /// Wrap (nat -> nat) (fun x => x + base)
  /// BUG: The raw lambda type is stored in std::any,
  /// but unwrap tries any_cast<std::function<...>>.
  static wrap pack_fn_direct(uint64_t base);
  static inline const uint64_t test_pack_fn_direct = []() {
    wrap w = pack_fn_direct(UINT64_C(10));
    return unwrap<std::function<uint64_t(uint64_t)>>(std::move(w))(UINT64_C(5));
  }();

  /// TEST 5: Pack a composed closure (let-bound, safe path).
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static wrap pack_composed(F0 &&f, uint64_t base) {
    std::function<uint64_t(uint64_t)> g = [=](uint64_t x) mutable {
      return (f(x) + base);
    };
    return wrap::wrap0(g);
  }

  static inline const uint64_t test_pack_composed = []() {
    wrap w = pack_composed([](uint64_t x) { return (x * UINT64_C(2)); },
                           UINT64_C(5));
    return unwrap<std::function<uint64_t(uint64_t)>>(std::move(w))(
        UINT64_C(10));
  }();
  /// TEST 6: Multiple wraps and unwraps.
  static inline const uint64_t test_multi_wrap = []() {
    wrap w1 = wrap::wrap0(UINT64_C(10));
    wrap w2 = wrap::wrap0(UINT64_C(20));
    return (unwrap<uint64_t>(std::move(w1)) + unwrap<uint64_t>(std::move(w2)));
  }();
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
