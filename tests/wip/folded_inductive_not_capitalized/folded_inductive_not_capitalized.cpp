#include "folded_inductive_not_capitalized.h"

Dval Helper::mk(Nat n) { return Dval::dv_nat(std::move(n)); }

Dval FoldedInductiveNotCapitalized::go(const Nat &x0_) {
  return Helper::mk(x0_);
}
