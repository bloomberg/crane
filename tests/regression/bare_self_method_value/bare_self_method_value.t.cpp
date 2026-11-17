#include <bare_self_method_value.h>
#include <cassert>

static int int_of(const Nat &n) {
  int k = 0;
  const Nat *p = &n;
  while (std::holds_alternative<typename Nat::S>(p->v())) {
    p = std::get<typename Nat::S>(p->v()).a0.get();
    k++;
  }
  return k;
}

int main() {
  assert(int_of(BareSelfMethodValue::example) == 3);
  return 0;
}
