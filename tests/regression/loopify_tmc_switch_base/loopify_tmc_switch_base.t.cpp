// A tail-modulo-cons loop whose base cases sit inside an enum's switch: the
// loop must return from there, not break out of the switch alone and spin.
#include "loopify_tmc_switch_base.h"

#include <cassert>
#include <iostream>

int main() {
  using M = LoopifyTmcSwitchBase;
  assert(M::run_f(M::Color::BLUE, 1) == 2);
  assert(M::run_f(M::Color::BLUE, 2) == 0);
  assert(M::run_f(M::Color::RED, 4) == 1);
  assert(M::run_f(M::Color::GREEN, 5) == 4);
  assert(M::run_f(M::Color::RED, 9) == 5);
  assert(M::run_f(M::Color::GREEN, 10) == 4);
  assert(M::run_f(M::Color::RED, 3000) == 1002);
  assert(M::run_f(M::Color::GREEN, 3001) == 1001);
  std::cout << "loopify_tmc_switch_base: run_f(RED, 3000)="
            << M::run_f(M::Color::RED, 3000) << " PASSED" << std::endl;
  return 0;
}
