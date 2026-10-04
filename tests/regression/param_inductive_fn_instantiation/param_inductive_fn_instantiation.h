#ifndef INCLUDED_PARAM_INDUCTIVE_FN_INSTANTIATION
#define INCLUDED_PARAM_INDUCTIVE_FN_INSTANTIATION

#include "crane_fn.h"
#include "fn.h"
#include <cstdint>
#include <type_traits>
#include <utility>
#include <variant>

/// A parameterised inductive with a function field
/// (`endo A := E : (A -> A) -> endo A`) instantiated at a function type: the
/// argument's nested binders must stay curried to match the field's
/// `std::function<F(F)>` type.
struct ParamInductiveFnInstantiation {
  template <typename A> struct endo {
    // DATA
    crane::fn<A(A)> a0;

    // ACCESSORS
    endo<A> clone() const { return {a0}; }

    template <typename CraneU> operator endo<CraneU>() const {
      return {crane_convert<crane::fn<CraneU(CraneU)>>(a0)};
    }

    // CREATORS
    static endo<A> e(crane::fn<A(A)> a0) { return {std::move(a0)}; }
  };

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, const crane::fn<T1(T1)> &>
  static T2 endo_rect(F0 &&f, const endo<T1> &e) {
    const auto &[a0] = e;
    return f(a0);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, const crane::fn<T1(T1)> &>
  static T2 endo_rec(F0 &&f, const endo<T1> &e) {
    const auto &[a0] = e;
    return f(a0);
  }

  template <typename T1> static T1 run(const endo<T1> &e, const T1 &x) {
    const auto &[a0] = e;
    return a0(x);
  }

  static inline const endo<crane::fn<uint64_t(uint64_t)>> d = []() {
    return endo<crane::fn<uint64_t(uint64_t)>>::e(
        [](crane::fn<uint64_t(uint64_t)> g) {
          return [=](uint64_t n) { return g(g(n)); };
        });
  }();
  static inline const uint64_t go = run<crane::fn<uint64_t(uint64_t)>>(
      d, [](uint64_t n) { return (n + UINT64_C(1)); })(UINT64_C(0));
};

#endif // INCLUDED_PARAM_INDUCTIVE_FN_INSTANTIATION
