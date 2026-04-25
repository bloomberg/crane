#include <todo_nested_module_type.h>

#include <concepts>
#include <memory>
#include <type_traits>

__attribute__((pure)) TodoNestedModuleType::NatOuter::Inner::t
TodoNestedModuleType::NatOuter::step(unsigned int n) {
  return (n + 1);
}
