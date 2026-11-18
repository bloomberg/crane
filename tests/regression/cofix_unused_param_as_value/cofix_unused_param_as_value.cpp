#include "cofix_unused_param_as_value.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// A cofixpoint whose parameter is unused (CoFixpoint c1 (n : nat) :=
/// sconst 0), passed unapplied to map, prints as the call c1(): "too
/// few arguments to function call, single argument '_x' was not
/// specified".  Naming a cofixpoint calls it only where it takes no
/// parameters.
CofixUnusedParamAsValue::stream CofixUnusedParamAsValue::sconst(uint64_t n) {
  return stream::lazy_(
      [=]() -> typename CofixUnusedParamAsValue::stream::SCons {
        return {n, sconst(n)};
      });
}

CofixUnusedParamAsValue::stream CofixUnusedParamAsValue::c1(uint64_t) {
  return sconst(UINT64_C(0));
}
