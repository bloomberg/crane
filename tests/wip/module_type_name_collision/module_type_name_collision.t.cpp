#include <module_type_name_collision.h>

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
  // double 3 = 6, then S = 7.
  auto r = ModuleTypeNameCollision::use(nat_of(3));
  assert(std::holds_alternative<Opt<Nat>::Some>(r.v()));
  assert(to_uint(std::get<Opt<Nat>::Some>(r.v()).x) == 7);
  return 0;
}
