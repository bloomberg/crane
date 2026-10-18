#include <cassert>
#include <collision_struct_concept_names_struct.h>
#include <iostream>

static unsigned to_unsigned(const Nat &n) {
  unsigned k = 0;
  for (const Nat *p = &n; std::holds_alternative<Nat::S>(p->v()); ++k) {
    p = std::get<Nat::S>(p->v()).a0.get();
  }
  return k;
}

int main() {
  unsigned sz = to_unsigned(CollisionStructConceptNamesStruct::sz);
  std::cout << sz << std::endl;
  assert(sz == 6);
  return 0;
}
