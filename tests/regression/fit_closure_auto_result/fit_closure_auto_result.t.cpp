#include <fit_closure_auto_result.h>

#include <cassert>

int main() {
  using M = FitClosureAutoResult;
  assert(M::via_hd_or == 3);
  assert(M::via_twice == 4);
  assert(M::via_nth_or == 5);
  assert(M::via_pick);
  return 0;
}
