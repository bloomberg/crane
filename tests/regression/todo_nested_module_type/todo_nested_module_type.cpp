#include <todo_nested_module_type.h>

__attribute__((pure)) TodoNestedModuleType::NatOuter::Inner::t
TodoNestedModuleType::NatOuter::step(unsigned int n) {
  return (n + 1);
}
