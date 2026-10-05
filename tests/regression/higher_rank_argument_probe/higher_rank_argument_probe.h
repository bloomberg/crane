#ifndef INCLUDED_HIGHER_RANK_ARGUMENT_PROBE
#define INCLUDED_HIGHER_RANK_ARGUMENT_PROBE

#include "fn.h"
#include "obj.h"

enum class Bool0;
enum class Bool0 { TRUE_, FALSE_ };

struct HigherRankArgumentProbe {
  static Bool0 call_poly(crane::fn<crane::obj(crane::obj)> f);
  static constexpr Bool0 sample = Bool0::TRUE_;
};

#endif // INCLUDED_HIGHER_RANK_ARGUMENT_PROBE
