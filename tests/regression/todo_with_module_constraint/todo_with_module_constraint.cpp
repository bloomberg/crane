#include <todo_with_module_constraint.h>

#include <type_traits>

__attribute__((pure)) TodoWithModuleConstraint::NatOuter::Inner::t
TodoWithModuleConstraint::NatOuter::step(const unsigned int n) {
  return (n + 1);
}
