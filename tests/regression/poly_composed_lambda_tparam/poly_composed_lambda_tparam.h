#pragma once

#include "fn.h"
#include <concepts>
#include <cstdint>
#include <utility>

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// In a polymorphic definition with a class constraint, composing two
/// let-bound lambdas (cf (cg c) where cg : nat -> A) prints a type that
/// names T1 outside any template: "use of undeclared identifier 'T1'".

template <typename I, typename A>
concept Sz = requires {
  { I::sz(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

struct PolyComposedLambdaTparam {
  struct sz_bool {
    constexpr static uint64_t sz(bool b) {
      if (b) {
        return UINT64_C(1);
      } else {
        return UINT64_C(0);
      }
    }
  };

  static_assert(Sz<sz_bool, bool>);

  template <typename _tcI0, typename T1>
    requires Sz<_tcI0, T1>
  static std::pair<bool, uint64_t> f(T1 a, uint64_t x0_) {
    crane::fn<std::pair<bool, uint64_t>(T1)> cf =
        [](const T1 &) { return std::make_pair(true, UINT64_C(0)); };
    crane::fn<T1(uint64_t)> cg = [=, a = std::move(a)](uint64_t) { return a; };
    return cf(cg(x0_));
  }

  static inline const uint64_t t = (
      f<sz_bool, bool>(true, UINT64_C(3)).second +
      (f<sz_bool, bool>(false, UINT64_C(4)).first ? UINT64_C(1) : UINT64_C(0)));
};
