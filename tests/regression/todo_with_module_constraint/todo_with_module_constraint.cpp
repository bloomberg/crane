#include <todo_with_module_constraint.h>

#include <type_traits>
#include <utility>

__attribute__((pure)) TodoWithModuleConstraint::NatOuter::Inner::t
TodoWithModuleConstraint::NatOuter::step(const unsigned int n) {
  return (std::move(n) + 1);
}
