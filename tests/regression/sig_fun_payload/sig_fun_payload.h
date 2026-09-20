#ifndef INCLUDED_SIG_FUN_PAYLOAD
#define INCLUDED_SIG_FUN_PAYLOAD

#include "crane_fn.h"
#include <any>
#include <functional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct Sig;

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  template <typename _U> operator Sig<_U>() const {
    return {[&]() -> _U {
      if constexpr (std::is_same_v<A, std::any>) {
        return crane_any_cast<_U>(x);
      } else {
        if constexpr (std::is_constructible_v<_U, const A &>) {
          return _U(x);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }
    }()};
  }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

struct SigFunPayload {
  static inline const Sig<std::function<uint64_t(uint64_t)>> mk =
      Sig<std::function<uint64_t(uint64_t)>>::exist(
          [](uint64_t x) { return (x + UINT64_C(1)); });
  static inline const uint64_t go = []() {
    const auto &_sv0 = mk;
    const auto &[x0] = _sv0;
    return x0(UINT64_C(4));
  }();
};

#endif // INCLUDED_SIG_FUN_PAYLOAD
