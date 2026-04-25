#include <todo_with_type_constraint.h>

#include <concepts>
#include <memory>
#include <type_traits>

__attribute__((pure)) unsigned int
TodoWithTypeConstraint::NatBase::bump(unsigned int n) {
  return (n + 1);
}
