#include "case_insensitive_eponymy.h"

Nat CaseInsensitiveEponymy::use(const cfg<Nat> &g) {
  return Other::size0(CFG0::template size<Nat>(g));
}

Nat Other::size0(Nat n) { return Nat::s(std::move(n)); }
