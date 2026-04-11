#include <modpath_escape_collision.h>

#include <type_traits>

__attribute__((pure)) unsigned int
ModpathEscapeCollision::A::Token_::f(const unsigned int n) {
  return n;
}

__attribute__((pure)) unsigned int
ModpathEscapeCollision::B::Token_::g(const unsigned int n) {
  return (n + 1);
}
