// WIP: this test does not build yet.
//
// A definition whose return type is an `if` over a boolean computing `nat` in
// one branch and `nat -> nat` in the other erases to `std::any`, which is then
// applied as a function.
#include "dependent_if_type_branches.h"

#include <cassert>
#include <iostream>

int main() {
  assert(DependentIfTypeBranches::go == 49);
  std::cout << "dependent_if_type_branches: go = " << DependentIfTypeBranches::go << " PASSED" << std::endl;
  return 0;
}
