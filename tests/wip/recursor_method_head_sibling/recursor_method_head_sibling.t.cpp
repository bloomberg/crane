// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Expected: extraction fails under CRANE_CHECK_IR (method head).
// When fixed: prints "recursor_method_head_sibling: ok".
#include <recursor_method_head_sibling.h>

#include <cassert>
#include <cstdint>
#include <iostream>

using M = RecursorMethodHeadSibling;

int main() {
  uint64_t n = M::sample.expr_rect<uint64_t>(
      [](const uint64_t &a) -> uint64_t { return a; },
      [](const bool &) -> uint64_t { return 0; },
      [](const auto &, uint64_t m) -> uint64_t { return m + 1; });
  assert(n == 2);
  std::cout << "recursor_method_head_sibling: ok\n";
  return 0;
}
