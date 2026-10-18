#include <cassert>
#include <iostream>
#include <moved_struct_method_after_collision.h>

static unsigned to_unsigned(const Nat &n) {
  unsigned k = 0;
  for (const Nat *p = &n; std::holds_alternative<Nat::S>(p->v()); ++k) {
    p = std::get<Nat::S>(p->v()).a0.get();
  }
  return k;
}

int main() {
  unsigned sz = to_unsigned(MovedStructMethodAfterCollision::sz);
  std::cout << sz << std::endl;
  assert(sz == 7);
  return 0;
}
