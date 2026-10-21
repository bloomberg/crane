// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <record_destructure_once.h>

#include <cassert>
#include <iostream>

int main() {
  using M = RecordDestructureOnce;

  std::cout << "steps = " << M::r_steps << std::endl;
  assert(M::r_steps == 40u);
  std::cout << "twice = " << M::r_twice << std::endl;
  assert(M::r_twice == 80u);
  std::cout << "zero = " << M::r_zero << std::endl;
  assert(M::r_zero == 0u);

  std::cout << "All record_destructure_once tests passed!" << std::endl;
  return 0;
}
