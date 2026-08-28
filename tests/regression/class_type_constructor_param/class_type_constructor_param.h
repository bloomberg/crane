#ifndef INCLUDED_CLASS_TYPE_CONSTRUCTOR_PARAM
#define INCLUDED_CLASS_TYPE_CONSTRUCTOR_PARAM

#include "crane_fn.h"
#include <any>
#include <concepts>
#include <functional>
#include <utility>

/// A typeclass parameterised by a type constructor (`Container (F : Type ->
/// Type)`). The higher-kinded parameter is demoted to a promoted associated
/// type holding the element-erased carrier, so the concept, the instance and
/// the method wrappers all agree.

template <typename I>
concept Container = requires {
  typename I::F;
  {
    I::cmap(std::declval<std::function<std::any(std::any)>>(),
            std::declval<typename I::F>())
  } -> std::convertible_to<typename I::F>;
  { I::cwrap(std::declval<std::any>()) } -> std::convertible_to<typename I::F>;
  { I::cout(std::declval<typename I::F>()) } -> std::convertible_to<std::any>;
};

struct ClassTypeConstructorParam {
  template <Container _tcI0, typename T2 = std::any, typename T3 = std::any,
            typename F0 = std::any>
  static typename _tcI0::F cmap(F0 &&x, const typename _tcI0::F &x0) {
    return crane_any_cast<typename _tcI0::F>(
        _tcI0::cmap(crane_erase_fn(x), x0));
  }

  template <Container _tcI0, typename T2>
  static typename _tcI0::F cwrap(const T2 &x) {
    return crane_any_cast<typename _tcI0::F>(_tcI0::cwrap(x));
  }

  template <Container _tcI0, typename T2>
  static T2 cout(const typename _tcI0::F &x) {
    return std::any_cast<T2>(_tcI0::cout(x));
  }

  struct IdC {
    using F = std::any;

    static std::any cmap(std::function<std::any(std::any)> f, std::any a0) {
      return f(a0);
    }

    static std::any cwrap(std::any x) { return x; }

    static std::any cout(std::any x) { return x; }
  };

  static_assert(Container<IdC>);
  static inline const uint64_t go =
      cout<IdC, uint64_t>(cmap<IdC, uint64_t, uint64_t>(
          [](uint64_t n) { return (n + UINT64_C(1)); },
          cwrap<IdC, uint64_t>(UINT64_C(4))));
};

#endif // INCLUDED_CLASS_TYPE_CONSTRUCTOR_PARAM
