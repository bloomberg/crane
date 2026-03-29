#include <todo_nested_module_type.h>

#include <type_traits>
#include <utility>

__attribute__((pure)) TodoNestedModuleType::NatOuter::Inner::t
TodoNestedModuleType::NatOuter::step(const unsigned int n) {
  return (std::move(n) + 1);
}
