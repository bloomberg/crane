#ifndef INCLUDED_CLASS_TYPE_CONSTRUCTOR_PARAM
#define INCLUDED_CLASS_TYPE_CONSTRUCTOR_PARAM

#include <any>
#include <concepts>
#include <functional>
#include <type_traits>
#include <utility>

/// WIP: A typeclass parameterised by a type constructor (`Container (F : Type
/// -> Type)`) collapses every method to `std::any` and generates a
/// one-type-argument concept, so the static assertion fails and the method
/// calls do not resolve.

template <typename I, typename F>
concept Container = requires {
  {
    I::cmap(std::declval<std::function<std::any(std::any)>>(),
            std::declval<F>())
  } -> std::convertible_to<F>;
  { I::cwrap(std::declval<std::any>()) } -> std::convertible_to<F>;
  { I::cout(std::declval<F>()) } -> std::convertible_to<std::any>;
};

struct ClassTypeConstructorParam {
  template <typename _tcI0, typename T1, typename T2, typename T3, typename F0>
    requires Container<_tcI0, T1> && std::is_invocable_r_v<T3, F0 &, T2 &>
  static T1 cmap(F0 &&x, const T1 &x0) {
    return std::any_cast<T1>(_tcI0::cmap(x, x0));
  }

  template <typename _tcI0, typename T1, typename T2>
    requires Container<_tcI0, T1>
  static T1 cwrap(const T2 &x) {
    return std::any_cast<T1>(_tcI0::cwrap(x));
  }

  template <typename _tcI0, typename T1, typename T2>
    requires Container<_tcI0, T1>
  static T2 cout(const T1 &x) {
    return std::any_cast<T2>(_tcI0::cout(x));
  }

  struct IdC {
    static std::any cmap(std::function<std::any(std::any)> f) { return f; }

    static std::any cwrap(std::any x) { return x; }

    static std::any cout(std::any x) { return x; }
  };

  static_assert(Container<IdC, std::any>);
  static inline const uint64_t go = cout<IdC>(cmap<IdC>(
      [](uint64_t n) { return (n + UINT64_C(1)); }, cwrap<IdC>(UINT64_C(4))));
};

#endif // INCLUDED_CLASS_TYPE_CONSTRUCTOR_PARAM
