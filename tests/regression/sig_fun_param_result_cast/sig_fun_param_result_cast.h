#ifndef INCLUDED_SIG_FUN_PARAM_RESULT_CAST
#define INCLUDED_SIG_FUN_PARAM_RESULT_CAST

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

/// A sig whose payload is a function, passed as a parameter (so its C++ type
/// is the concrete Sig<std::function<uint64_t(uint64_t)>>), must be applied
/// directly rather than through an erased-function cast.
struct SigFunParamResultCast {
  static uint64_t apply_sig(const Sig<std::function<uint64_t(uint64_t)>> &f,
                            uint64_t n);
  static inline const Sig<std::function<uint64_t(uint64_t)>> idf =
      Sig<std::function<uint64_t(uint64_t)>>::exist(
          [](uint64_t n) { return n; });
  static inline const uint64_t go = apply_sig(idf, UINT64_C(2));
};

#endif // INCLUDED_SIG_FUN_PARAM_RESULT_CAST
