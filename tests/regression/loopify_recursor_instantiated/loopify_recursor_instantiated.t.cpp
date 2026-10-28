// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_recursor_instantiated.h>

#include <cassert>
#include <cstdint>
#include <iostream>

using M = LoopifyRecursorInstantiated;

#ifndef DEPTH
#define DEPTH 100000
#endif

// The recursor at motive uint64_t, counting nodes as size does.
static uint64_t count(const M::expr &e) {
  return M::expr_rect<uint64_t>(
      [](const uint64_t &) -> uint64_t { return 1; },
      [](const bool &) -> uint64_t { return 1; },
      [](const auto &, uint64_t n) -> uint64_t { return n + 1; },
      [](const auto &, uint64_t c, const auto &, uint64_t t, const auto &,
         uint64_t f) -> uint64_t { return c + t + f + 1; },
      [](const auto &, uint64_t x, const auto &, uint64_t y) -> uint64_t {
        return x + y + 1;
      },
      [](const auto &, uint64_t p) -> uint64_t { return p + 1; }, e);
}

int main() {
  assert(M::run == 5);
  assert(count(M::sample) == 5);
  // A succE chain deep enough that a C++ call of expr_rect per level would
  // exhaust the stack.  It is never destroyed: expr, an indexed family, has
  // no iterative destructor, and tearing it down would overflow the stack.
  M::expr *e = new M::expr(M::expr::lit(0));
  for (int i = 0; i < DEPTH; ++i) {
    *e = M::expr::succe(std::move(*e));
  }
  assert(M::size<uint64_t>(*e) == DEPTH + 1);
  assert(count(*e) == DEPTH + 1);
  std::cout << "loopify_recursor_instantiated: ok\n";
  return 0;
}
