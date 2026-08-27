// A typeclass instance at a function type (`Sz (nat -> nat)`): the instance
// method's parameter is concrete, so calling it must not go through the
// erased `std::any` adapter.
#include "instance_at_function_type.h"

#include <cassert>
#include <iostream>

int main() {
  assert(InstanceAtFunctionType::go == 7);
  std::cout << "instance_at_function_type: go = " << InstanceAtFunctionType::go << " PASSED" << std::endl;
  return 0;
}
