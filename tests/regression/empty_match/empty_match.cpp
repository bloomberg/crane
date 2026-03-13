#include <empty_match.h>

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

__attribute__((pure)) unsigned int
EmptyMatch::from_empty(const std::shared_ptr<EmptyMatch::empty> &_x0) {
  return absurd<unsigned int>(_x0);
}
