#ifndef INCLUDED_HIGHER_RANK_ARGUMENT_PROBE
#define INCLUDED_HIGHER_RANK_ARGUMENT_PROBE

#include "crane_fn.h"
#include <any>
#include <functional>

enum class Bool0 { TRUE_, FALSE_ };

struct HigherRankArgumentProbe {
  static Bool0 call_poly(std::function<std::any(std::any)> f);
  static inline const Bool0 sample = call_poly(
      crane_erase_fn([](const auto &x) { return std::any_cast<Bool0>(x); }));
};

#endif // INCLUDED_HIGHER_RANK_ARGUMENT_PROBE
