#include "local_lifted_mutual_closure_back.h"

/// A lifted local mutual group (local_lifted_mutual) whose member f
/// passes its partner g a lambda over its own callable, and g passes
/// it back to f.  A lambda in a function template has a new closure type
/// in every instantiation, so were g to deduce its callable, f<T1, L1>
/// would instantiate g<T1, L2>, whose callable f deduces, whose lambda
/// is L3, and so on without end.  Of a lifted local group only a
/// self-call was looked at (detect_non_forwarded_params_fix); a partner's
/// closure is weighed as a top-level group's is
/// (closure_feedback_params, mutual_lambda_other_instance): g takes
/// a crane::fn, f keeps deducing.
uint64_t LocalLiftedMutualClosureBack::run(uint64_t k, uint64_t n) {
  return (run_crane_f(
              [](const List<uint64_t> &_x) { return _x.length(); },
              List<uint64_t>::cons(
                  UINT64_C(1),
                  List<uint64_t>::cons(
                      UINT64_C(2), List<uint64_t>::cons(
                                       UINT64_C(3), List<uint64_t>::nil()))),
              n, k) +
          run_crane_f(
              [](bool b) -> uint64_t {
                if (b) {
                  return UINT64_C(1);
                } else {
                  return UINT64_C(2);
                }
              },
              true, n, k));
}
