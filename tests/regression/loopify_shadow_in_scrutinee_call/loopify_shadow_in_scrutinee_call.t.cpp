#include <loopify_shadow_in_scrutinee_call.h>

#include <cassert>
#include <cstdio>

static unsigned to_int(const Nat &n) {
  unsigned k = 0;
  const Nat *p = &n;
  while (std::holds_alternative<Nat::S>(p->v())) {
    ++k;
    p = std::get<Nat::S>(p->v()).a0.get();
  }
  return k;
}

int main() {
  // firstn 3, 2, 1 of [5; 7; 9] all start with 5.
  assert(to_int(LoopifyShadowInScrutineeCall::total) == 15);
  std::printf("loopify_shadow_in_scrutinee_call: ok\n");
  return 0;
}
