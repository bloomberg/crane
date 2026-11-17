// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Only the function the per-function setting selects rebuilds its uniquely
// owned input in place: its result is made of the input's cells, the other
// function's result of new ones.
#include <cassert>
#include <set>
#include <utility>
#include <variant>
#include "reuse_per_function_on.h"

using M = ReusePerFunctionOn;

// The cons cells behind the list's tail pointers.
static std::set<const void *> cells(const M::lst &l) {
  std::set<const void *> out;
  const M::lst *cur = &l;
  while (auto *c = std::get_if<M::lst::Cons>(&cur->v())) {
    cur = &*c->a1;
    if (std::holds_alternative<M::lst::Cons>(cur->v())) out.insert(cur);
  }
  return out;
}

int main() {
  M::lst a = M::upto(100);
  std::set<const void *> before = cells(a);
  M::lst a2 = M::incr_reused(std::move(a));
  assert(M::sum(a2) == 5050 + 100);
  assert(cells(a2) == before);

  // Offered for consuming, which only an owned parameter would accept.
  M::lst b = M::upto(100);
  std::set<const void *> in = cells(b);
  M::lst b2 = M::incr_fresh(std::move(b));
  assert(M::sum(b2) == 5050 + 200);
  assert(M::sum(b) == 5050);
  for (const void *p : cells(b2)) assert(in.count(p) == 0);
  return 0;
}
