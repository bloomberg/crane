// WIP: this test does not build yet.
//
// A parameterised inductive with a function field (`endo A := E : (A -> A) -> endo A`)
// instantiated at a function type emits an uncurried two-parameter lambda for
// a field of curried `std::function` type.
#include "param_inductive_fn_instantiation.h"

#include <cassert>
#include <iostream>

int main() {
  assert(ParamInductiveFnInstantiation::go == 2);
  std::cout << "param_inductive_fn_instantiation: go = " << ParamInductiveFnInstantiation::go << " PASSED" << std::endl;
  return 0;
}
