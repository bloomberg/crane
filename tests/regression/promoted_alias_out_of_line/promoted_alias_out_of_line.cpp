#include "promoted_alias_out_of_line.h"

Nat Other::size0(const Nat &n) { return Nat::s(n); }

Nat F::size(Nat n) { return n; }
