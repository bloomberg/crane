// A definition whose return type is a dependent [if] computing nat in one
// branch and nat -> nat in the other erases to std::any: the returned closure
// is stored through the canonical adapter and cast back at the call site.
#include "dependent_if_type_branches.h"

#include <cassert>
#include <iostream>

int main() {
  assert(DependentIfTypeBranches::go == 49);
  std::cout << "dependent_if_type_branches: go = " << DependentIfTypeBranches::go << " PASSED" << std::endl;
  return 0;
}
