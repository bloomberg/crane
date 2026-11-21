// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <immortal_sticky_count.h>
#include <cassert>
#include <cstddef>
#include <vector>

using M = ImmortalStickyCount;
using Tree = M::tree;

// A sticky count: far above any count a program reaches, far below wrapping.
static bool sticky(const Tree &t) { return t.v().use_count() >= ~std::size_t{0} / 4; }

static bool all_sticky(const Tree &t) {
  auto *n = crane::get_if<Tree::Node>(&t.v());
  return !n || (sticky(t) && all_sticky(*n->a0) && all_sticky(*n->a2));
}

int main() {
  assert(crane::get_if<Tree::Node>(&M::table.v()) && all_sticky(M::table));
  // Copies and drops move the count, never off the sticky range.
  {
    const std::size_t before = M::table.v().use_count();
    std::vector<Tree> copies(100000, M::table);
    assert(M::table.v().use_count() == before + 100000 && sticky(M::table));
  }
  assert(M::sizes(1000, 0) == 1000 * 15);
  assert(M::table.v().use_count() == ~std::size_t{0} / 2);
  assert(all_sticky(M::table));
  // A value built at run time is counted from one.
  {
    Tree t = M::fresh(3);
    assert(t.v().use_count() == 1);
    Tree u = t;
    assert(t.v().use_count() == 2);
  }
  return 0;
}
