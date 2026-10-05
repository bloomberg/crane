#include "higher_rank_argument_probe.h"

Bool0 HigherRankArgumentProbe::call_poly(
    const crane::fn<crane::obj(crane::obj)> &f) {
  return crane::any_cast<Bool0>(f(Bool0::TRUE_));
}
