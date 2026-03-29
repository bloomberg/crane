#include <escape_collision.h>

#include <type_traits>
#include <utility>

__attribute__((pure)) unsigned int
EscapeCollision::double_(const unsigned int n) {
  return std::move(n);
}

__attribute__((pure)) unsigned int
EscapeCollision::double_0(const unsigned int n) {
  return (std::move(n) + 1);
}
