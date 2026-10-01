#include <loopify_adopted_fix_name_shared.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = LoopifyAdoptedFixNameShared::r1;
  assert(r.has_value());
  int k = 0;
  const Nat *p = &*r;
  while (auto *s = std::get_if<Nat::S>(&p->v())) { k++; p = s->a0.get(); }
  assert(k == 8);
  std::cout << "loopify_adopted_fix_name_shared: ok" << std::endl;
  return 0;
}
