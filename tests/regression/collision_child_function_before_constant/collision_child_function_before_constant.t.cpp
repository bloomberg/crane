#include <cassert>
#include <collision_child_function_before_constant.h>
#include <iostream>

static unsigned to_unsigned(const Nat &n) {
  unsigned k = 0;
  for (const Nat *p = &n; std::holds_alternative<Nat::S>(p->v()); ++k) {
    p = std::get<Nat::S>(p->v()).a0.get();
  }
  return k;
}

int main() {
  unsigned c = to_unsigned(CollisionChildFunctionBeforeConstant::c);
  std::cout << c << std::endl;
  assert(c == 5);
  return 0;
}
