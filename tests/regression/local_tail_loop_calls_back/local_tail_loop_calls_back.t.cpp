// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <local_tail_loop_calls_back.h>

#include <cassert>
#include <cstdio>

int main() {
  using M = LocalTailLoopCallsBack;
  using T = M::tree;
  // Two million leaves under one node: [scan] steps over all but the last,
  // which as a lambda calling itself overflows the stack.
  const uint64_t n = 2000000;
  List<T> leaves = List<T>::nil();
  for (uint64_t i = n; i > 0; --i) {
    leaves = List<T>::cons(T::leaf(i), std::move(leaves));
  }
  const T root = T::node(std::move(leaves));
  assert(M::find(root, 0) == std::optional<uint64_t>(1));
  assert(M::find(root, n - 1) == std::optional<uint64_t>(n));
  assert(!M::find(root, n).has_value());
  std::printf("local_tail_loop_calls_back: ok\n");
  return 0;
}
