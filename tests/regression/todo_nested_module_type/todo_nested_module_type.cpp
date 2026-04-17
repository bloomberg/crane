#include <todo_nested_module_type.h>

#include <concepts>
#include <type_traits>

__attribute__((pure)) TodoNestedModuleType::NatOuter::Inner::t
TodoNestedModuleType::NatOuter::step(const unsigned int n) {
  return (n + 1);
}
