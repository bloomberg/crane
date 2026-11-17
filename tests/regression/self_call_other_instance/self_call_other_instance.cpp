#include "self_call_other_instance.h"

/// f calls itself at bool, not at its own A, passing a lambda over
/// bool.  Extraction instantiates the call at bool, so the lambda is
/// [](bool b) and translation writes the call f<bool>.  The function's
/// generation replaces every other reference to itself with the reference
/// at its own template parameters (glob_subst_stmt with rec_call in
/// gen_functions.ml); this one it spares, since the call's use solves A
/// to a ground type (other_instance_self_calls).  Respelled f<T1>, it
/// would take no lambda over bool once f is called at a list.  The same
/// pair across two functions is mutual_lambda_ground_instance.
uint64_t SelfCallOtherInstance::run(uint64_t n) {
  return f<List<uint64_t>>(
      [](const List<uint64_t> &_x) { return _x.length(); },
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))),
      n);
}
