#include <cassert>
#include <stated_precondition_param_unused.h>
#include <variant>

static unsigned to_unsigned(const Nat &n) {
  unsigned k = 0;
  const Nat *p = &n;
  while (auto *s = std::get_if<Nat::S>(&p->v())) {
    ++k;
    p = s->a0.get();
  }
  return k;
}

int main() {
  assert(to_unsigned(StatedPreconditionParamUnused::result) == 3);
  return 0;
}
