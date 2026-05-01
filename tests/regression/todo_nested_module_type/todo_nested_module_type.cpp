#include <todo_nested_module_type.h>

TodoNestedModuleType::NatOuter::Inner::t
TodoNestedModuleType::NatOuter::step(const unsigned int n) {
  return (n + 1);
}
