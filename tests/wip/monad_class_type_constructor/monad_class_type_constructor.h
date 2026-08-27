#ifndef INCLUDED_MONAD_CLASS_TYPE_CONSTRUCTOR
#define INCLUDED_MONAD_CLASS_TYPE_CONSTRUCTOR

#include "crane_fn.h"
#include <any>
#include <concepts>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

/// WIP: A monad typeclass over a type constructor (`Mon (M : Type -> Type)`)
/// emits the instance name in value position (`MOpt` used as a value), and the
/// bind body applies a `std::any`.

template <typename I, typename M>
concept Mon = requires {
  { I::mret(std::declval<std::any>()) } -> std::convertible_to<M>;
  {
    I::mbind(std::declval<M>(), std::declval<std::function<M(std::any)>>())
  } -> std::convertible_to<M>;
};

struct MonadClassTypeConstructor {
  template <typename _tcI0, typename T1, typename T2>
    requires Mon<_tcI0, T1>
  static T1 mret(const T2 &x) {
    return std::any_cast<T1>(_tcI0::mret(x));
  }

  template <typename _tcI0, typename T1, typename T2, typename F1>
    requires Mon<_tcI0, T1> && std::is_invocable_r_v<T1, F1 &, T2 &>
  static T1 mbind(const T1 &x, F1 &&x0) {
    return std::any_cast<T1>(_tcI0::mbind(x, x0));
  }

  template <typename a> using Opt = std::optional<a>;

  struct MOpt {
    static std::optional<std::any> mret(std::any a) {
      return std::make_optional<std::any>(crane_erase_fn(a));
    }

    static std::optional<std::any>
    mbind(std::optional<std::any> m,
          std::function<std::optional<std::any>(std::any)> f) {
      if (m.has_value()) {
        const auto &a = *m;
        return crane_call_erased(f, a);
      } else {
        return std::optional<std::any>();
      }
    }
  };

  static_assert(Mon<MOpt, std::optional<std::any>>);
  static inline const Opt<uint64_t> prog =
      mbind(MOpt, mret(MOpt, UINT64_C(20)),
            [](uint64_t a) { return mret(MOpt, (a + UINT64_C(22))); });
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
