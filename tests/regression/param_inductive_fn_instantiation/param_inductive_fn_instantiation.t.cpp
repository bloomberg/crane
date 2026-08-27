// A parameterised inductive with a function field
// (`endo A := E : (A -> A) -> endo A`) instantiated at a function type: the
// argument's nested binders must stay curried to match the field's
// `std::function<F(F)>` type.
#include "param_inductive_fn_instantiation.h"

#include <cassert>
#include <iostream>

int main() {
  assert(ParamInductiveFnInstantiation::go == 2);
  std::cout << "param_inductive_fn_instantiation: go = " << ParamInductiveFnInstantiation::go << " PASSED" << std::endl;
  return 0;
}
