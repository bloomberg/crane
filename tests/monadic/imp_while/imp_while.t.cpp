// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <imp_while.h>

#include <iostream>

namespace {
int failures = 0;
void check(bool ok, const char *what) {
  if (!ok) {
    std::cout << "FAILED: " << what << std::endl;
    ++failures;
  }
}
} // namespace

int main() {
  auto [fsteps, fvars] = ImpWhile::run_factorial(5);
  check(ImpWhile::nth(1, fvars, 0) == 120, "factorial 5 = 120");
  check(ImpWhile::nth(0, fvars, 0) == 0, "factorial counts down to 0");
  std::cout << "factorial 5: " << ImpWhile::nth(1, fvars, 0) << " in "
            << fsteps << " steps" << std::endl;

  auto [bsteps, bvars] = ImpWhile::run_fibonacci(20);
  check(ImpWhile::nth(1, bvars, 0) == 6765, "fibonacci 20 = 6765");
  std::cout << "fibonacci 20: " << ImpWhile::nth(1, bvars, 0) << " in "
            << bsteps << " steps" << std::endl;

  auto [ssteps, svars] = ImpWhile::run_square(30);
  check(ImpWhile::nth(2, svars, 0) == 900, "square 30 = 900");
  std::cout << "square 30: " << ImpWhile::nth(2, svars, 0) << " in "
            << ssteps << " steps" << std::endl;

  if (failures == 0) {
    std::cout << "imp_while: all tests passed" << std::endl;
  }
  return failures;
}
