// Tail modulo cons through a partner's inlined body, whose recursive call
// Normalize bound to a temporary.  Extracted under CRANE_CHECK_IR, which used
// to reject the plan's chains; deep inputs check the loops take the calls.
#include "loopify_mutual_tmc_temporary.h"

#include <cassert>
#include <iostream>

int main() {
  using M = LoopifyMutualTmcTemporary;
  assert(M::run_ea(7) == 4);
  assert(M::run_eb(7, 3) == 3);
  assert(M::run_eb(8, 3) == 4);
  assert(M::run_da(M::Color::RED, 9) == 0);
  assert(M::run_da(M::Color::GREEN, 9) == 1);
  assert(M::run_db(9) == 1);
  assert(M::run_db(10) == 0);
  assert(M::run_ea(10000) == 5000);
  assert(M::run_eb(10001, 3) == 5000);
  assert(M::run_db(9999) == 1);
  assert(M::run_da(M::Color::GREEN, 10000) == 2);
  std::cout << "loopify_mutual_tmc_temporary: run_ea(10000)="
            << M::run_ea(10000) << " run_db(9999)=" << M::run_db(9999)
            << " PASSED" << std::endl;
  return 0;
}
