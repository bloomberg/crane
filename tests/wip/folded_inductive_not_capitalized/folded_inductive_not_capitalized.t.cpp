#include "folded_inductive_not_capitalized.h"
#include <cassert>

int main() {
  auto d = FoldedInductiveNotCapitalized::go(Nat::s(Nat::o()));
  assert(std::holds_alternative<Helper::Dval::DV_nat>(d.v()));
  return 0;
}
