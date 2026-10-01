#include <loopify_fix_captures_class_param.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = LoopifyFixCapturesClassParam::result;
  assert(r.has_value());
  int k = 0;
  const Nat *p = &*r;
  while (auto *s = std::get_if<Nat::S>(&p->v())) { k++; p = s->a0.get(); }
  assert(k == 6);
  std::cout << "loopify_fix_captures_class_param: ok" << std::endl;
  return 0;
}
