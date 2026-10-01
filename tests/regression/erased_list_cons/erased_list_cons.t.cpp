// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression test for the "erased-context unresolved type variable" codegen bug:
// a list-consing semantic action stored in an erased grammar-entry slot must not
// emit `crane::any_cast<Datatypes::List<T1>>` with an unsubstituted type variable.
// Merely compiling the generated header (whose namespace-scope `entries` global
// instantiates the erased action) fails before the fix with
// "use of undeclared identifier 'T1'".

#include "erased_list_cons.h"

int main() {
  // Reference the global so its initializer (the erased action) is required.
  (void)&entries;
  return 0;
}
