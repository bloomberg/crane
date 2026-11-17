#include "mutual_lambda_ground_instance.h"

/// f calls its partner g at bool, not at its own A, passing a
/// lambda over bool.  Extraction typed a call within the recursive group
/// at the group's own variables whatever it was written at, so the
/// lambda's binder took f's variable: [](const T1 &b) { if (b) ... },
/// no C++ once f is called at a list.  A type argument written as a
/// ground type instantiates the partner like any other constant.  g
/// calls back with a named function, whose type is the same at every
/// instance; a lambda there is mutual_lambda_other_instance.
uint64_t MutualLambdaGroundInstance::dbl(uint64_t k) { return (k + k); }

uint64_t MutualLambdaGroundInstance::run(uint64_t n) {
  return f<List<uint64_t>>(
      [](const List<uint64_t> &_x) { return _x.length(); },
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))),
      n);
}
