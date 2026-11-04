// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <fast_variant_assign_from_own_child.h>

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <utility>

using M = FastVariantAssignFromOwnChild;
using C = M::chain;

// [n] down to 1, then [Last end].
static C build(std::uint64_t n, std::uint64_t end) {
  C c = C::last(end);
  for (std::uint64_t i = 1; i <= n; ++i) c = C::link(i, std::move(c));
  return c;
}

static C &tail(C &c) { return *get_if<C::Link>(&c.v_mut())->a1; }

int main() {
  C c = build(5, 0);
  assert(M::total(c) == 15);
  c = tail(c); // a copy of a part of itself, the same alternative
  assert(M::total(c) == 10);
  c = std::move(tail(c)); // a part of itself moved in
  assert(M::total(c) == 6);
  C d = build(1, 7);
  d = tail(d); // a copy of a part of itself, another alternative
  assert(M::total(d) == 7);
  C e = build(1, 9);
  e = std::move(tail(e));
  assert(M::total(e) == 9);
  // A part shared with another holder stays the other's too.
  C f = build(3, 0);
  C g = f;
  f = tail(f);
  assert(M::total(f) == 3 && M::total(g) == 6);
  std::printf("fast_variant_assign_from_own_child: ok\n");
  return 0;
}
