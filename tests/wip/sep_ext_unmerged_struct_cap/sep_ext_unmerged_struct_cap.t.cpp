// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// WIP: When Module Exprs contains Inductive expr, the inner struct
// is defined as `struct expr` (lowercase) but referenced as `Exprs::Expr`
// (capitalized), causing "no type named 'Expr' in Exprs" errors.
// The definition and reference should use consistent capitalization.

#include "SepExtUnmergedStructCap.h"
#include "Datatypes.h"

int main() {
  const auto e = SepExtUnmergedStructCap::UseExprs::make_neg(
      SepExtUnmergedStructCap::Exprs::expr::lit(Datatypes::Nat::o()));
  (void)e;
  return 0;
}
