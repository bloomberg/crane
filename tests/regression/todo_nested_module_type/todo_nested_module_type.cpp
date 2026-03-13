#include <todo_nested_module_type.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) TodoNestedModuleType::NatOuter::Inner::t
TodoNestedModuleType::NatOuter::step(const unsigned int n) {
  return (std::move(n) + 1);
}
