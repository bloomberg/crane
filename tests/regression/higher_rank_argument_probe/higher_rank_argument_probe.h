#ifndef INCLUDED_HIGHER_RANK_ARGUMENT_PROBE
#define INCLUDED_HIGHER_RANK_ARGUMENT_PROBE

#include "crane_fn.h"
#include <any>
#include <type_traits>

enum class Bool0 { TRUE_, FALSE_ };

struct HigherRankArgumentProbe {
  template <typename F0>
    requires std::is_invocable_r_v<std::any, F0 &, std::any &>
  static Bool0 call_poly(F0 &&f) {
    return std::any_cast<Bool0>(f(Bool0::TRUE_));
  }

  static inline const Bool0 sample =
      call_poly(crane_erase_fn([](const auto &x) { return x; }));
};

#endif // INCLUDED_HIGHER_RANK_ARGUMENT_PROBE
