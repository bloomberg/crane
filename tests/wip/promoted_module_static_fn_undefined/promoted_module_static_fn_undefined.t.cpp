#include <promoted_module_static_fn_undefined.h>
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
  // Sizes 0 and 1, each plus one.
  assert(int_of(PromotedModuleStaticFnUndefined::example(Nat::o())) == 3);
  return 0;
}
