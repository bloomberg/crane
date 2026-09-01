#ifndef INCLUDED_MONAD_CLASS_TYPE_CONSTRUCTOR
#define INCLUDED_MONAD_CLASS_TYPE_CONSTRUCTOR

#include <any>
#include <concepts>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

/// A monad typeclass over a type constructor (`Mon (M : Type -> Type)`), with a
/// carrier (`Opt`) that is itself a definition.  Exercises the higher-kinded
/// class parameter together with an erased callback passed to `mbind`.

template <typename I>
concept Mon = requires {
  typename I::template M<std::any>;
  {
    I::mret(std::declval<std::any>())
  } -> std::convertible_to<typename I::template M<std::any>>;
  {
    I::mbind(std::declval<typename I::template M<std::any>>(),
             std::declval<
                 std::function<typename I::template M<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template M<std::any>>;
};

struct MonadClassTypeConstructor {
  template <Mon _tcI0, typename T2>
  static typename _tcI0::template M<T2> mret(const T2 &x) {
    return _tcI0::template mret<T2>(x);
  }

  template <Mon _tcI0, typename T2, typename T3, typename F1>
    requires std::is_invocable_r_v<typename _tcI0::template M<T3>, F1 &, T2 &>
  static typename _tcI0::template M<T3> mbind(typename _tcI0::template M<T2> x,
                                              F1 &&x0) {
    return _tcI0::template mbind<T2, T3>(x, x0);
  }

  template <typename a> using Opt = std::optional<a>;

  struct MOpt {
    template <typename _A0> using M = std::optional<_A0>;

    template <typename _A0 = std::any> static std::optional<_A0> mret(_A0 a) {
      return std::make_optional<_A0>(a);
    }

    template <typename _A0 = std::any, typename _A1 = std::any>
    static std::optional<_A1> mbind(std::optional<_A0> m,
                                    std::function<std::optional<_A1>(_A0)> f) {
      if (m.has_value()) {
        const _A0 &a = *m;
        return f(a);
      } else {
        return std::optional<_A1>();
      }
    }
  };

  static_assert(Mon<MOpt>);
  static inline const Opt<uint64_t> prog = mbind<MOpt, uint64_t, uint64_t>(
      mret<MOpt, uint64_t>(UINT64_C(20)),
      [](uint64_t a) { return mret<MOpt, uint64_t>((a + UINT64_C(22))); });
  static inline const uint64_t go = []() -> uint64_t {
    if (prog.has_value()) {
      const uint64_t &n = *prog;
      return n;
    } else {
      return UINT64_C(0);
    }
  }();
};

#endif // INCLUDED_MONAD_CLASS_TYPE_CONSTRUCTOR
