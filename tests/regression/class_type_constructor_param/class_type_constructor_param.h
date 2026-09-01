#ifndef INCLUDED_CLASS_TYPE_CONSTRUCTOR_PARAM
#define INCLUDED_CLASS_TYPE_CONSTRUCTOR_PARAM

#include <any>
#include <concepts>
#include <functional>
#include <type_traits>
#include <utility>

/// A typeclass parameterised by a type constructor (`Container (F : Type ->
/// Type)`). The higher-kinded parameter is demoted to a promoted associated
/// type holding the element-erased carrier, so the concept, the instance and
/// the method wrappers all agree.

template <typename I>
concept Container = requires {
  typename I::template F<std::any>;
  {
    I::template cmap<std::any, std::any>(
        std::declval<std::function<std::any(std::any)>>(),
        std::declval<typename I::template F<std::any>>())
  } -> std::convertible_to<typename I::template F<std::any>>;
  {
    I::template cwrap<std::any>(std::declval<std::any>())
  } -> std::convertible_to<typename I::template F<std::any>>;
  {
    I::template cout<std::any>(std::declval<typename I::template F<std::any>>())
  } -> std::convertible_to<std::any>;
};

struct ClassTypeConstructorParam {
  template <Container _tcI0, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T2 &>
  static typename _tcI0::template F<T3>
  cmap(F0 &&x, typename _tcI0::template F<T2> x0) {
    return _tcI0::template cmap<T2, T3>(x, x0);
  }

  template <Container _tcI0, typename T2>
  static typename _tcI0::template F<T2> cwrap(const T2 &x) {
    return _tcI0::template cwrap<T2>(x);
  }

  template <Container _tcI0, typename T2>
  static T2 cout(typename _tcI0::template F<T2> x) {
    return _tcI0::template cout<T2>(x);
  }

  struct IdC {
    template <typename _A0> using F = _A0;

    template <typename _A0, typename _A1>
    static _A1 cmap(std::function<_A1(_A0)> f, _A0 a0) {
      return f(a0);
    }

    template <typename _A0> static _A0 cwrap(_A0 x) { return x; }

    template <typename _A0> static _A0 cout(_A0 x) { return x; }
  };

  static_assert(Container<IdC>);
  static inline const uint64_t go =
      cout<IdC, uint64_t>(cmap<IdC, uint64_t, uint64_t>(
          [](uint64_t n) { return (n + UINT64_C(1)); },
          cwrap<IdC, uint64_t>(UINT64_C(4))));
};

#endif // INCLUDED_CLASS_TYPE_CONSTRUCTOR_PARAM
