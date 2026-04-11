#include <escape_collision.h>

#include <type_traits>

__attribute__((pure)) unsigned int
EscapeCollision::double_(const unsigned int n) {
  return n;
}

__attribute__((pure)) unsigned int
EscapeCollision::double_0(const unsigned int n) {
  return (n + 1);
}
