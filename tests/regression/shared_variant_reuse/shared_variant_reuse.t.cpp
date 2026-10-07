// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <shared_variant_reuse.h>
#include <cassert>
#include <utility>

using M = SharedVariantReuse;
using Tree = SharedVariantReuse::tree;
using Lst = SharedVariantReuse::lst;

// The block a tree's root lives in, or null for a leaf.
static const void *root(const Tree &t) {
  return crane::get_if<Tree::Node>(&t.v());
}

int main() {
  // Unique: each update writes into the blocks along its path.
  Tree t = Tree::leaf();
  for (uint64_t k : {5, 3, 8, 1, 4, 7, 9})
    t = M::insert(k, k * 10, std::move(t));
  const void *r0 = root(t);
  t = M::insert(4, 44, std::move(t));
  assert(root(t) == r0);
  t = M::insert(5, 55, std::move(t));
  assert(root(t) == r0);
  assert(*t.find(4) == 44 && *t.find(5) == 55 && *t.find(9) == 90);

  // Shared: the update copies the path, and the other holder keeps the old
  // tree.
  Tree keep = t;
  Tree u = M::insert(4, 444, std::move(t));
  assert(root(u) != r0 && root(keep) == r0);
  assert(*u.find(4) == 444 && *keep.find(4) == 44);

  // A list mapped in place: the head block is the same, the values bumped.
  Lst l = Lst::cons(1, Lst::cons(2, Lst::cons(3, Lst::nil())));
  const void *h0 = crane::get_if<Lst::Cons>(&l.v());
  l = M::bump(std::move(l));
  assert(crane::get_if<Lst::Cons>(&l.v()) == h0);
  assert(l.total() == 2 + 3 + 4);
  return 0;
}
