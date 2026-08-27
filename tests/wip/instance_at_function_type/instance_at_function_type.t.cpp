// WIP: this test does not build yet.
//
// A typeclass instance at a function type (`Sz (nat -> nat)`) inserts an
// `any_cast<std::function<std::any(std::any)>>` on a parameter whose C++ type
// is already the concrete `std::function<uint64_t(uint64_t)>`.
#include "instance_at_function_type.h"

#include <cassert>
#include <iostream>

int main() {
  assert(InstanceAtFunctionType::go == 7);
  std::cout << "instance_at_function_type: go = " << InstanceAtFunctionType::go << " PASSED" << std::endl;
  return 0;
}
