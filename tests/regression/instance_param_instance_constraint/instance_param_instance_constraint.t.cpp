// An instance parameterised by another instance (`Def A -> Def (option A)`)
// used at `option (option nat)`: the nested instantiation must list the
// instance argument before the type argument.
#include "instance_param_instance_constraint.h"

#include <cassert>
#include <iostream>

int main() {
  assert(InstanceParamInstanceConstraint::go == 9);
  std::cout << "instance_param_instance_constraint: go = " << InstanceParamInstanceConstraint::go << " PASSED" << std::endl;
  return 0;
}
