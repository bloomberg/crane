// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// A rebuilt node shares the cells of the children it reads out of a matched
// value; children without fields share one cell.
#include <shared_child_cells.h>
#include <cassert>
#include <variant>

using M = SharedChildCells;
using Tree = SharedChildCells::tree;

static const Tree::Node &node(const Tree &t) { return std::get<Tree::Node>(t.v()); }

int main() {
  Tree t = Tree::leaf();
  for (uint64_t k : {5, 3, 8, 1, 4, 7, 9})
    t = M::insert(k, t);
  assert(M::sum(t) == 37);

  // Inserting 6 rebuilds the path 5 -> 8 -> 7; 5's left child (3, 1, 4)
  // and 8's right child (9) are the old tree's cells.
  Tree u = M::insert(6, t);
  assert(M::sum(u) == 43 && M::sum(t) == 37);
  assert(node(u).l.get() == node(t).l.get());
  assert(node(*node(u).r).r.get() == node(*node(t).r).r.get());
  assert(node(u).r.get() != node(t).r.get());

  // Both children of a leaf-only node are one cell.
  Tree one = M::insert(2, Tree::leaf());
  assert(node(one).l.get() == node(one).r.get());

  // Swapped children keep their cells.
  Tree m = M::mirror_root(t);
  assert(node(m).l.get() == node(t).r.get() && node(m).r.get() == node(t).l.get());
  assert(M::sum(m) == 37);
  return 0;
}
