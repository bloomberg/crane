// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Repro: let cofix capturing outer n causes infinite recursion.
//
// fibst_repro's inner lambda captures [n] by [&] from fibst_repro's
// parameter.  In the S branch, [_x = n - 1] computes the predecessor but
// is never used to update [n], so every recursive call still sees the
// original value.  Calling fibst_repro(5) overflows the stack.
#include "fibst_cofix_repro.h"

#include <iostream>

int main() {
  auto result = fibst_repro<FibstCofixReproTests::nat_stref,
                            FibstCofixReproTests::nat_idx,
                            uint64_t>(5);
  std::cout << "fibst_repro(5) = " << result << std::endl;
  return 0;
}
