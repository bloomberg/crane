// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <local_lambda_refs.h>

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
  using M = LocalLambdaRefs;
  check(M::bump_twice == 7, "bump_twice = 3 + 4");
  check(M::bump_each.first == 3, "bump_each: first reference bumped 3 times");
  check(M::bump_each.second == 14, "bump_each: second reference bumped 4 times");
  const auto &[xs, ys] = M::fill_each;
  check(M::nth(0, xs, 0) == 1 && M::nth(1, xs, 0) == 2 && M::nth(2, xs, 0) == 3, "fill_each: [1; 2; 3]");
  check(M::nth(0, ys, 0) == 1 && M::nth(1, ys, 0) == 2, "fill_each: [1; 2]");
  if (failures == 0) {
    std::cout << "local_lambda_refs: all tests passed" << std::endl;
  }
  return failures;
}
