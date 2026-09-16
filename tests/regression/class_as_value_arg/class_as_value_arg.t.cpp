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

// A class is a concept, so the instance meeting it is a type, supplied as a
// template argument rather than as a value.
struct Width8 {
  static Nat width() { return nat_of(8); }
};

int main() {
  // width 8 + tag 1 = 9.
  assert(to_uint(ClassAsValueArg::use<Width8>(memory_bit{nat_of(1)})) == 9);
  return 0;
}
