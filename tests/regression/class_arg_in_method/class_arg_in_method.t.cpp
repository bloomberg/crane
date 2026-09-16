#include <class_arg_in_method.h>

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

// The class is a concept, so an instance of it is a type.
struct Width8 {
  static Nat width() { return nat_of(8); }
};

int main() {
  // Byte 3 under width 8 is 11.
  assert(to_uint(ClassArgInMethod::use<Width8>(Memory_bit::byte(nat_of(3)))) ==
         11);
  return 0;
}
