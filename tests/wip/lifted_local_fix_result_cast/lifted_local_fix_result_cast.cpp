#include "lifted_local_fix_result_cast.h"

/// A local fixpoint with a type binder of its own is lifted to a template
/// returning its variable, T1 f_crane_go(List<T1>, T1).  Called at a
/// record under a projection, its result is cast to the enclosing
/// function's return type, crane::any_cast<bool>(f_crane_go(..)).py,
/// where it is the record: it does not compile.
bool LiftedLocalFixResultCast::f(uint64_t) {
  return crane::any_cast<bool>(
      f_crane_go(List<LiftedLocalFixResultCast::pt>::cons(
          pt{UINT64_C(1), true}, List<LiftedLocalFixResultCast::pt>::nil()),
                 pt{UINT64_C(0), false}))
             .py;
}
