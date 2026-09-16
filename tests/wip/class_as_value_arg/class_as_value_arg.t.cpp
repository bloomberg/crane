#include <class_as_value_arg.h>

#include <cassert>
#include <variant>

static Nat nat_of(unsigned n) {
  Nat r = Nat::o();
  for (unsigned i = 0; i < n; ++i) r = Nat::s(std::move(r));
  return r;
}

static unsigned to_uint(const Nat &n) {
  unsigned c = 0;
  const Nat *p = &n;
  while (std::holds_alternative<Nat::S>(p->v())) {
    ++c;
    p = std::get<Nat::S>(p->v()).a0.get();
  }
  return c;
}

int main() {
  // width 8 + tag 1 = 9.
  assert(to_uint(ClassAsValueArg::use(Params{nat_of(8)}, memory_bit{nat_of(1)})) == 9);
  return 0;
}
