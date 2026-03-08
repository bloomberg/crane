#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <todo_with_type_constraint.h>
#include <variant>

unsigned int TodoWithTypeConstraint::NatBase::bump(const unsigned int n) {
  return (std::move(n) + 1);
}
