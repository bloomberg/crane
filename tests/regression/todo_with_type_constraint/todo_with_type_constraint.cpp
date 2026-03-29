#include <todo_with_type_constraint.h>

#include <type_traits>
#include <utility>

__attribute__((pure)) unsigned int
TodoWithTypeConstraint::NatBase::bump(const unsigned int n) {
  return (std::move(n) + 1);
}
