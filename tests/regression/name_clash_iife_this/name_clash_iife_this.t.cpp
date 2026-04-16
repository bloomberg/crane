#include <name_clash_iife_this.h>

#include <cassert>

int main() {
  using NS = NameClashIifeThis;

  auto c5 = NS::shape::circle(5);
  auto s34 = NS::shape::square(3, 4);

  // match_of_match: inner match on color, Blue branch returns the shape arg.
  // Previously generated `return this` inside the IIFE (compile error).
  assert(NS::match_of_match(NS::Color::e_RED, c5) == 10u);   // Circle 5 -> r*2 = 10
  assert(NS::match_of_match(NS::Color::e_GREEN, c5) == 7u);  // Square 3 4 -> 3+4 = 7
  assert(NS::match_of_match(NS::Color::e_BLUE, c5) == 10u);  // s=circle(5) -> r*2 = 10
  assert(NS::match_of_match(NS::Color::e_BLUE, s34) == 7u);  // s=square(3,4) -> 3+4 = 7

  return 0;
}
