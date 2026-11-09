#include "mutual_lambda_other_instance.h"

/// f calls its partner g at another instance, g bool, than its own,
/// passing a lambda over bool, and g passes it back to f.  A lambda
/// in a function template has a new closure type in every instantiation, so
/// were g to take it as a deduced callable, g<bool, L1> would
/// instantiate f<bool, L1 &>, whose lambda L2 instantiates g<bool,
/// L2>, and so on without end.  The lambda's type flows back into the
/// instantiation that makes it, so g takes it as a crane::fn
/// (partner_closure_params).  With a named callback instead the cycle
/// closes and g deduces it (splice_partner_other_instance), as it does
/// where g does not pass it back (mutual_lambda_ground_instance).
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
