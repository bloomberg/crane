#include "stated_precondition_param_unused.h"

/// C++ cannot check m <= n of a nat witness, so the precondition is
/// stated in a comment that spells n, written _x: the body never reads
/// it.  A comment reads nothing, so n stays unnamed, or
/// -Werror,-Wunused-parameter rejects the function.
Nat StatedPreconditionParamUnused::get(
    const Nat &, const Sig<Nat> &b) { // Precondition: b <= _x
  const auto &[x] = b;
  return x;
}
