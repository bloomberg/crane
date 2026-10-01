#include <instance_chain_constraint.h>

#include <cassert>
#include <iostream>

int main() {
  assert(InstanceChainConstraint::is_ok);
  std::cout << "instance_chain_constraint: ok" << std::endl;
  return 0;
}
