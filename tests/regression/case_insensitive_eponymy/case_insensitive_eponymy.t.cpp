#include <case_insensitive_eponymy.h>

#include <cassert>
#include <variant>

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
  // size of a one-block cfg is 1, then Other.size gives 2.
  assert(to_uint(CaseInsensitiveEponymy::use(
             cfg<Nat>{Nat::o(), List<Nat>::cons(Nat::o(), List<Nat>::nil())})) ==
         2);
  return 0;
}
