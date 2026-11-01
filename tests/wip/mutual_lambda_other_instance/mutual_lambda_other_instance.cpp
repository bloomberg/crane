#include "mutual_lambda_other_instance.h"

/// f calls its partner g at another instance, g bool, than its own,
/// passing a lambda over bool.  Type reconstruction solves a call within
/// a recursive group at the group's own variables, so the lambda's binder
/// is typed at f's variable: [](const T1 &b) { if (b) ... }, which does
/// not compile once f is called at a list.  The call itself is written
/// at bool (g<bool>); only what it reconstructs inside the group is
/// not.  splice_partner_other_instance is the same pair with a named
/// function, which has no binder to type.
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
