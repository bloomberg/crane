#include <modpath_escape_collision.h>

#include <memory>
#include <type_traits>

__attribute__((pure)) unsigned int
ModpathEscapeCollision::A::Token_::f(unsigned int n) {
  return n;
}

__attribute__((pure)) unsigned int
ModpathEscapeCollision::B::Token_::g(unsigned int n) {
  return (n + 1);
}
