#ifndef INCLUDED_HIGHER_RANK_ARGUMENT_PROBE
#define INCLUDED_HIGHER_RANK_ARGUMENT_PROBE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"

enum class Bool0;
enum class Bool0 { TRUE_, FALSE_ };

struct HigherRankArgumentProbe {
  static Bool0 call_poly(crane::fn<crane::obj(crane::obj)> f);
  static inline const Bool0 sample =
      call_poly(crane_erase_fn([](const auto &x) { return x; }));
};

#endif // INCLUDED_HIGHER_RANK_ARGUMENT_PROBE
