#ifndef INCLUDED_CLASS_TYPE_CONSTRUCTOR_PARAM
#define INCLUDED_CLASS_TYPE_CONSTRUCTOR_PARAM

#include "fn.h"
#include "obj.h"
#include <concepts>
#include <cstdint>
#include <type_traits>
#include <utility>

/// A typeclass parameterised by a type constructor (`Container (F : Type ->
/// Type)`). The higher-kinded parameter is demoted to a promoted associated
/// type holding the element-erased carrier, so the concept, the instance and
/// the method wrappers all agree.

template <typename I>
concept Container = requires {
  typename I::template F<crane::obj>;
  {
    I::template cmap<crane::obj, crane::obj>(
        std::declval<crane::fn<crane::obj(crane::obj)>>(),
        std::declval<typename I::template F<crane::obj>>())
  } -> std::convertible_to<typename I::template F<crane::obj>>;
  {
    I::template cwrap<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template F<crane::obj>>;
  {
    I::template cout<crane::obj>(
        std::declval<typename I::template F<crane::obj>>())
  } -> std::convertible_to<crane::obj>;
};

struct ClassTypeConstructorParam {
  template <Container _tcI0, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T2 &>
  static typename _tcI0::template F<T3>
  cmap(F0 &&x, typename _tcI0::template F<T2> x0) {
    return _tcI0::template cmap<T2, T3>(x, std::move(x0));
  }

  template <Container _tcI0, typename T2>
  static typename _tcI0::template F<T2> cwrap(const T2 &x) {
    return _tcI0::template cwrap<T2>(x);
  }

  template <Container _tcI0, typename T2>
  static T2 cout(typename _tcI0::template F<T2> x) {
    return _tcI0::template cout<T2>(std::move(x));
  }

  struct IdC {
    template <typename CraneA0> using F = CraneA0;

    template <typename CraneA0, typename CraneA1>
    static CraneA1 cmap(crane::fn<CraneA1(CraneA0)> f, CraneA0 a0) {
      return f(std::move(a0));
    }

    template <typename CraneA0> static CraneA0 cwrap(CraneA0 x) { return x; }

    template <typename CraneA0> static CraneA0 cout(CraneA0 x) { return x; }
  };

  static_assert(Container<IdC>);
  static inline const uint64_t go =
      cout<IdC, uint64_t>(cmap<IdC, uint64_t, uint64_t>(
          [](uint64_t n) { return (n + UINT64_C(1)); },
          cwrap<IdC, uint64_t>(UINT64_C(4))));
};

#endif // INCLUDED_CLASS_TYPE_CONSTRUCTOR_PARAM
