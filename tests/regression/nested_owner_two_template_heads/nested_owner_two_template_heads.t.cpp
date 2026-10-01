#include "nested_owner_two_template_heads.h"
#include <cassert>
#include <cstdio>

int main() {
  auto one = Nat::s(Nat::o());
  auto two = Nat::s(one);
  auto b = Bag::bag<Nat>::add(one, Bag::bag<Nat>::add(two, Bag::bag<Nat>::empty()));
  assert(count_odd_is(b, one));
  assert(!count_odd_is(b, two));
  assert(count_odd_is(Bag::bag<Nat>::empty(), Nat::o()));
  assert(std::holds_alternative<Bag::bag<Nat>::Add>(round(b).v()));
  printf("All nested_owner_two_template_heads tests passed!\n");
  return 0;
}
