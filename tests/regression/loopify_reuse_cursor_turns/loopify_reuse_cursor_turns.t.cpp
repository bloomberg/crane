// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_reuse_cursor_turns.h>

#include <cassert>
#include <cstdio>
#include <vector>

using M = LoopifyReuseCursorTurns;
using L = M::lst;

// [n; n-1; ...; 1]
static L down(std::uint64_t n) {
  L l = L::nil();
  for (std::uint64_t i = 1; i <= n; ++i) l = L::cons(i, std::move(l));
  return l;
}

static std::vector<std::uint64_t> items(const L &l) {
  std::vector<std::uint64_t> out;
  for (const L *p = &l; std::holds_alternative<L::Cons>(p->v());) {
    const auto &c = std::get<L::Cons>(p->v());
    out.push_back(c.a0);
    p = c.a1.get();
  }
  return out;
}

using V = std::vector<std::uint64_t>;

int main() {
  // A turn building nothing walks on: the caller's shared suffix survives.
  {
    L m = down(5);
    L r = M::keep_even(L::cons(7, m));
    assert(items(r) == (V{4, 2}));
    assert(items(m) == (V{5, 4, 3, 2, 1}));
    assert(items(M::keep_even(down(8))) == (V{8, 6, 4, 2}));
  }
  // Two cells a turn: the second cell, shared with [m], keeps its fields.
  {
    L m = L::cons(3, down(4));
    L r = M::swap(L::cons(1, L::cons(2, m)));
    assert(items(r) == (V{2, 1, 4, 3, 2, 3, 1}));
    assert(items(m) == (V{3, 4, 3, 2, 1}));
    assert(items(M::swap(down(6))) == (V{5, 6, 3, 4, 1, 2}));
  }
  // The inner cell reads the element the outer one was rebuilt over.
  assert(items(M::stutter(down(3))) == (V{4, 3, 3, 2, 2, 1}));
  // The next accumulator reads it too.
  assert(items(M::scale(1, down(4))) == (V{4, 15, 16, 10}));
  // The cell reads the list it walks, whole, before its field is stolen.
  assert(items(M::suffix_sums(down(4))) == (V{10, 6, 3, 1}));
  // A shared list is left as it was.
  {
    L s = down(4);
    assert(items(M::stutter(s)) == (V{5, 4, 4, 3, 3, 2, 2, 1}));
    assert(items(s) == (V{4, 3, 2, 1}));
  }
  std::printf("loopify_reuse_cursor_turns: ok\n");
  return 0;
}
