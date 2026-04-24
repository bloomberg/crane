#include <name_clash_scrutinee.h>

#include <cassert>

int main() {
  using NS = NameClashScrutinee;

  // Sequential matches
  assert(NS::shape::circle(10).describe(NS::Color::e_RED) == 11u);
  assert(NS::shape::square(3, 4).describe(NS::Color::e_GREEN) == 9u);

  // Nested matches
  assert(NS::shape::circle(5).nested_match(NS::Color::e_RED) == 15u);
  assert(NS::shape::square(3, 4).nested_match(NS::Color::e_GREEN) == 7u);

  // Triple nesting
  assert(NS::wrapper::empty().triple_nest() == 0u);
  assert(NS::wrapper::wrap(NS::Color::e_RED, NS::shape::circle(7)).triple_nest() == 7u);
  assert(NS::wrapper::wrap(NS::Color::e_GREEN, NS::shape::square(3, 4)).triple_nest() == 12u);

  return 0;
}
