// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// bump_root, not recursive, rebuilds a unique root in its own block under
// Loopify; a root held elsewhere is copied and the other holder unchanged.
#include <reuse_loopified_helper.h>
#include <cassert>
#include <utility>

using M = ReuseLoopifiedHelper;
using Tree = ReuseLoopifiedHelper::tree;

static const void *root(const Tree &t) {
  return crane::get_if<Tree::Node>(&t.v());
}

int main() {
  Tree t = Tree::leaf();
  for (uint64_t k : {5, 3, 8, 1, 4})
    t = M::insert(k, t);
  assert(M::sum(t) == 21);

  const void *r0 = root(t);
  t = M::bump_root(std::move(t));
  assert(root(t) == r0);
  assert(M::sum(t) == 22);

  Tree keep = t;
  Tree u = M::bump_root(std::move(t));
  assert(root(u) != r0 && root(keep) == r0);
  assert(M::sum(u) == 23 && M::sum(keep) == 22);
  return 0;
}
