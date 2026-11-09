#include "local_lifted_mutual.h"

/// A local mutual group used at two types has type variables of its own,
/// so it is lifted out of run to function templates.  Every member was
/// lifted under the name of the member the group is projected to, and a
/// member's references to its partners were left as they were: f called
/// an undeclared g.  Each member is lifted to a helper of its own, and
/// reaches its partners as it reaches itself.  A partner passed a closure
/// that flows back is local_lifted_mutual_closure_back.
uint64_t LocalLiftedMutual::run(uint64_t k, uint64_t n) {
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
