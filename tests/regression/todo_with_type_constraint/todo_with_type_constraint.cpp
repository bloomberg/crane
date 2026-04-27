#include <todo_with_type_constraint.h>

__attribute__((pure)) unsigned int
TodoWithTypeConstraint::NatBase::bump(unsigned int n) {
  return (n + 1);
}
