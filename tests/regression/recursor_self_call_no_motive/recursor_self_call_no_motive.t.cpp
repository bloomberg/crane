// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <recursor_self_call_no_motive.h>

#include <cassert>
#include <cstdint>
#include <iostream>

using M = RecursorSelfCallNoMotive;

int main() {
  uint64_t n = M::expr_rect<uint64_t>(
      [](const uint64_t &) -> uint64_t { return 1; },
      [](const bool &) -> uint64_t { return 1; },
      [](const auto &, uint64_t m) -> uint64_t { return m + 1; },
      [](const auto &, uint64_t c, const auto &, uint64_t t, const auto &,
         uint64_t f) -> uint64_t { return c + t + f + 1; },
      [](const auto &, uint64_t x, const auto &, uint64_t y) -> uint64_t {
        return x + y + 1;
      },
      [](const auto &, uint64_t p) -> uint64_t { return p + 1; }, M::sample);
  assert(n == 5);
  std::cout << "recursor_self_call_no_motive: ok\n";
  return 0;
}
