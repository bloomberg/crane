#include "lifted_local_fix_result_cast.h"

/// A local fixpoint with a type binder of its own is lifted to a template
/// returning its variable, T1 f_crane_go(List<T1>, T1).  Called at a
/// record under a projection, its result is cast to the enclosing
/// function's return type, crane::any_cast<bool>(f_crane_go(..)).py,
/// where it is the record: it does not compile.  The body calls go as a
/// local whose type binder makes it higher-rank, so lowering read its
/// result back from a box, at the only type it had, the function's; the
/// template it is lifted to returns its result unboxed, and the call
/// standing for it is now the call alone.
bool LiftedLocalFixResultCast::f(uint64_t) {
  return f_crane_go(List<LiftedLocalFixResultCast::pt>::cons(
      pt{UINT64_C(1), true}, List<LiftedLocalFixResultCast::pt>::nil()),
                    pt{UINT64_C(0), false})
             .py;
}
