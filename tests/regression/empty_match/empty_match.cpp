#include <empty_match.h>

#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
EmptyMatch::from_empty(const EmptyMatch::empty &_x0) {
  return absurd<unsigned int>(_x0);
}
