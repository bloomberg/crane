#include "lifted_helper_same_binder_name.h"

uint64_t LiftedHelperSameBinderName::two(bool b, uint64_t n) {
  if (b) {
    return (two_crane_g(n).length() + two_crane_g(true).length());
  } else {
    return (
        two_crane_g_1(n).length() +
        two_crane_g_1(List<uint64_t>::cons(n, List<uint64_t>::nil())).length());
  }
}
