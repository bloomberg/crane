#include <promoted_alias_out_of_line.h>

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
  // Other.size (F.size 0) is 1; F.lst of the empty list is 0.
  assert(to_uint(PromotedAliasOutOfLine::use) == 1);
  assert(to_uint(F::lst(0, List<Dval<iptr>>::nil())) == 0);
  return 0;
}
