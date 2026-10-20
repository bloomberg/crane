// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <move_read_outside_region.h>

#include <cassert>
#include <iostream>

int main() {
  using M = MoveReadOutsideRegion;

  // s = [1; 2; 1; 2], grow s has 8 elements.
  std::cout << "if_in_argument = " << M::r_if_in_argument << std::endl;
  assert(M::r_if_in_argument == 4u);
  std::cout << "if_in_let = " << M::r_if_in_let << std::endl;
  assert(M::r_if_in_let == 20u);
  std::cout << "match_in_let = " << M::r_match_in_let << std::endl;
  assert(M::r_match_in_let == 20u);
  std::cout << "if_beside = " << M::r_if_beside << std::endl;
  assert(M::r_if_beside == 12u);
  std::cout << "match_beside = " << M::r_match_beside << std::endl;
  assert(M::r_match_beside == 12u);
  // aux n + aux b, each a list of n = 2 elements.
  std::cout << "helper_twice = " << M::r_helper_twice << std::endl;
  assert(M::r_helper_twice == 4u);

  std::cout << "All move_read_outside_region tests passed!" << std::endl;
  return 0;
}
