#include "folded_inductive_not_capitalized.h"
#include <cassert>

int main() {
  // A single-constructor inductive is a plain struct, not a variant, so the
  // field is read directly.
  Helper::Dval d = FoldedInductiveNotCapitalized::go(Nat::s(Nat::o()));
  assert(std::holds_alternative<Nat::S>(d.n.v()));
  return 0;
}
