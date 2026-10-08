// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <shared_variant_constant.h>
#include <cassert>
#include <cstdint>

using M = SharedVariantConstant;

static std::uint64_t value(const Positive &p) {
  if (auto *x = crane::get_if<Positive::XI>(&p.v())) return 2 * value(*x->a0) + 1;
  if (auto *x = crane::get_if<Positive::XO>(&p.v())) return 2 * value(*x->a0);
  return 1;
}

int main() {
  // The same block every time, and it stays put: no count can free it.
  const void *a = crane::get_if<Positive::XI>(&M::seven(std::monostate{}).v());
  const void *b = crane::get_if<Positive::XI>(&M::seven(std::monostate{}).v());
  assert(a != nullptr && a == b);
  assert(value(M::seven(std::monostate{})) == 7);
  // 6 = xO 3 and 12 = xO 6 share the closed subterm 3 = xI xH only if it is
  // the same constant; at least both values are right.
  auto p = M::pair_of(std::monostate{});
  assert(value(p.first) == 6 && value(p.second) == 12);
  assert(value(M::result) == 1 + 100 * 10);
  return 0;
}
