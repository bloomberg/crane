#ifndef INCLUDED_MONAD_CLASS_TYPE_CONSTRUCTOR
#define INCLUDED_MONAD_CLASS_TYPE_CONSTRUCTOR

#include "crane_fn.h"
#include <any>
#include <concepts>
#include <functional>
#include <memory>
#include <optional>
#include <utility>

template <typename I>
concept Mon = requires {
  typename I::M;
  { I::mret(std::declval<std::any>()) } -> std::convertible_to<typename I::M>;
  {
    I::mbind(std::declval<typename I::M>(),
             std::declval<std::function<typename I::M(std::any)>>())
  } -> std::convertible_to<typename I::M>;
};

struct MonadClassTypeConstructor {
  template <Mon _tcI0, typename T2> static typename _tcI0::M mret(const T2 &x) {
    return crane_any_cast<typename _tcI0::M>(_tcI0::mret(x));
  }

  template <Mon _tcI0, typename T2 = std::any, typename F1 = std::any>
  static typename _tcI0::M mbind(const typename _tcI0::M &x, F1 &&x0) {
    return crane_any_cast<typename _tcI0::M>(
        _tcI0::mbind(x, crane_erase_fn<typename _tcI0::M>(x0)));
  }

  template <typename a> using Opt = std::optional<std::any>;

  struct MOpt {
    using M = std::optional<std::any>;

    static std::optional<std::any> mret(std::any a) {
      return std::make_optional<std::any>(std::any(crane_erase_fn(a)));
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

  static_assert(Mon<MOpt>);
  static inline const Opt<std::any> prog =
      mbind<MOpt, uint64_t>(mret<MOpt, uint64_t>(UINT64_C(20)), [](uint64_t a) {
        return mret<MOpt, uint64_t>((a + UINT64_C(22)));
      });
  static inline const uint64_t go = []() -> uint64_t {
    if (prog.has_value()) {
      const auto &n = *prog;
      return std::any_cast<uint64_t>(n);
    } else {
      return UINT64_C(0);
    }
  }();
};

#endif // INCLUDED_MONAD_CLASS_TYPE_CONSTRUCTOR
