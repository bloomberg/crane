#include "todo_nested_module_type.h"

TodoNestedModuleType::NatOuter::Inner::t
TodoNestedModuleType::NatOuter::step(uint64_t n) {
  return (n + 1);
}
