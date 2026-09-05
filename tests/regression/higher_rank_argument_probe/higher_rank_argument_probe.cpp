#include "higher_rank_argument_probe.h"

Bool0 HigherRankArgumentProbe::call_poly(std::function<std::any(std::any)> f) {
  return std::any_cast<Bool0>(f(Bool0::TRUE_));
}
