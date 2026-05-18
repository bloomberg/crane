#include "todo_with_module_constraint.h"

TodoWithModuleConstraint::NatOuter::Inner::t
TodoWithModuleConstraint::NatOuter::step(uint64_t n) {
  return (n + 1);
}
