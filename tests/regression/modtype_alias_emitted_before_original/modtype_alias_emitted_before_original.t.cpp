#include "modtype_alias_emitted_before_original.h"
#include <cassert>
#include <cstdio>

int main() {
  auto one = Nat::s(Nat::o());
  auto two = Nat::s(one);
  assert(go(one, one));
  assert(!go(one, two));
  assert(std::holds_alternative<Nat::S>(tag2.v()));
  printf("All modtype_alias_emitted_before_original tests passed!\n");
  return 0;
}
