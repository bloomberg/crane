#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <todo_with_module_constraint.h>
#include <variant>

TodoWithModuleConstraint::NatOuter::Inner::t
TodoWithModuleConstraint::NatOuter::step(const unsigned int n) {
  return (std::move(n) + 1);
}
