#include <algorithm>
#include <any>
#include <empty_match.h>
#include <functional>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int
EmptyMatch::from_empty(const std::shared_ptr<EmptyMatch::empty> &_x0) {
  return absurd<unsigned int>(_x0);
}
