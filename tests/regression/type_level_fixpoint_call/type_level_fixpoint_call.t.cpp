// A Fixpoint returning Type erases to std::any: a value of type ty 1 is
// stored as an erased callable and applied through the canonical adapter.
#include "type_level_fixpoint_call.h"

#include <cassert>
#include <iostream>

int main() {
  assert(TypeLevelFixpointCall::go == 5);
  std::cout << "type_level_fixpoint_call: go = " << TypeLevelFixpointCall::go << " PASSED" << std::endl;
  return 0;
}
