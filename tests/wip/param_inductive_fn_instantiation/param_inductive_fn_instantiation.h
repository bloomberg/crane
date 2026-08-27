#ifndef INCLUDED_PARAM_INDUCTIVE_FN_INSTANTIATION
#define INCLUDED_PARAM_INDUCTIVE_FN_INSTANTIATION

#include <functional>
#include <type_traits>
#include <utility>
#include <variant>

/// WIP: A parameterised inductive with a function field (`endo A := E : (A ->
/// A) -> endo A`) instantiated at a function type emits an uncurried
/// two-parameter lambda for a field of curried `std::function` type.
struct ParamInductiveFnInstantiation {
  template <typename A> struct endo {
    // DATA
    std::function<A(A)> a0;

    // ACCESSORS
    endo<A> clone() const { return {a0}; }

    // CREATORS
    static endo<A> e(std::function<A(A)> a0) { return {std::move(a0)}; }
  };

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, std::function<T1(T1)> &>
  static T2 endo_rect(F0 &&f, const endo<T1> &e) {
    const auto &[a0] = e;
    return f(a0);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, std::function<T1(T1)> &>
  static T2 endo_rec(F0 &&f, const endo<T1> &e) {
    const auto &[a0] = e;
    return f(a0);
  }

  template <typename T1> static T1 run(const endo<T1> &e, const T1 &x) {
    const auto &[a0] = e;
    return a0(x);
  }

  static inline const endo<std::function<uint64_t(uint64_t)>> d =
      endo<std::function<uint64_t(uint64_t)>>::e(
          [](std::function<uint64_t(uint64_t)> g, uint64_t n) {
            return g(g(n));
          });
  static inline const uint64_t go = run<std::function<uint64_t(uint64_t)>>(
      d, [](uint64_t n) { return (n + UINT64_C(1)); })(UINT64_C(0));
};

#endif // INCLUDED_PARAM_INDUCTIVE_FN_INSTANTIATION
