#include <escape_collision.h>

#include <memory>
#include <type_traits>

__attribute__((pure)) unsigned int EscapeCollision::double_(unsigned int n) {
  return n;
}

__attribute__((pure)) unsigned int EscapeCollision::double_0(unsigned int n) {
  return (n + 1);
}
