#include <todo_with_type_constraint.h>

#include <type_traits>

__attribute__((pure)) unsigned int
TodoWithTypeConstraint::NatBase::bump(const unsigned int n) {
  return (n + 1);
}
