#include "mutual_lambda_other_instance.h"

/// f calls its partner g at another instance, g bool, than its own,
/// passing a lambda over bool, and g passes it back to f.  The lambda
/// is typed at bool (mutual_lambda_ground_instance), but both take it
/// as a deduced callable, and a lambda in a function template has a new
/// closure type in every instantiation: g<bool, L1> instantiates f<bool,
/// L1 &>, whose lambda L2 instantiates g<bool, L2>, and so on --
/// "recursive template instantiation exceeded maximum depth".  A self-call
/// passing anything but the parameter takes it as a crane::fn
/// (detect_non_forwarded_params); a partner's call is not looked at.
uint64_t MutualLambdaOtherInstance::run(uint64_t n) {
  return f<List<uint64_t>>(
      [](const List<uint64_t> &_x) { return _x.length(); },
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))),
      n);
}
