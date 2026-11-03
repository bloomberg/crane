// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <reuse_moved_capture_renamed.h>

#include <cassert>
#include <cstdio>

using M = ReuseMovedCaptureRenamed;
using T = M::tree;
using L = M::mylist<T>;

static T node(std::uint64_t v) { return T::node(T::leaf(), v, T::leaf()); }

int main() {
  // Owned: the closures take the trees out of the cells they recycle.
  L ts = L::mycons(node(1), L::mycons(T::leaf(), L::mycons(node(5), L::mynil())));
  assert(M::apply_all(M::adders(std::move(ts)), 10) == 11 + 10 + 15);
  // Shared: the caller's list keeps its trees.
  L shared = L::mycons(node(2), L::mycons(node(3), L::mynil()));
  assert(M::apply_all(M::adders(shared), 1) == 3 + 4);
  assert(M::apply_all(M::adders(shared), 0) == 2 + 3);
  std::printf("reuse_moved_capture_renamed: ok\n");
  return 0;
}
