// WIP: this test does not build yet.
//
// A `Fixpoint` returning `Type` erases to `std::any`; a value of type `ty 1`
// is then applied as a function, and `std::any` provides no call operator.
#include "type_level_fixpoint_call.h"

#include <cassert>
#include <iostream>

int main() {
  assert(TypeLevelFixpointCall::go == 5);
  std::cout << "type_level_fixpoint_call: go = " << TypeLevelFixpointCall::go << " PASSED" << std::endl;
  return 0;
}
