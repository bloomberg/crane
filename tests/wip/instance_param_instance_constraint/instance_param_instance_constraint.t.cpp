// WIP: this test does not build yet.
//
// An instance parameterised by another instance (`Def A -> Def (option A)`)
// used at `option (option nat)` emits a template instantiation whose concept
// constraints are not satisfied, plus a stray unqualified `dflt` reference.
#include "instance_param_instance_constraint.h"

#include <cassert>
#include <iostream>

int main() {
  assert(InstanceParamInstanceConstraint::go == 9);
  std::cout << "instance_param_instance_constraint: go = " << InstanceParamInstanceConstraint::go << " PASSED" << std::endl;
  return 0;
}
