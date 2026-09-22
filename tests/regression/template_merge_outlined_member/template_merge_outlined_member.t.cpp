#include "template_merge_outlined_member.h"
#include <cassert>
#include <cstdio>

int main() {
  auto two = Nat::s(Nat::s(Nat::o()));
  auto one = Nat::s(Nat::o());
  assert(sz_is(Box<Nat>::bx(Nat::o()), two));
  assert(sz_is(Box<Nat>::bnil(), one));
  assert(!sz_is(Box<Nat>::bnil(), two));
  assert(std::holds_alternative<Box<Nat>::Bx>(
      round(Box<Nat>::bx(Nat::o())).v()));
  printf("All template_merge_outlined_member tests passed!\n");
  return 0;
}
