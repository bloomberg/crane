#include <empty_match.h>

#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
EmptyMatch::from_empty(const std::shared_ptr<EmptyMatch::empty> &_x0) {
  return absurd<unsigned int>(_x0);
}
