// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// A loop-invariant parameter is moved on the frame machine's final path
// only when that path runs once and nothing reads the parameter after it.
#include <loopify_final_move.h>

#include <cstdint>
#include <iostream>

using T = LoopifyFinalMove;
using final_move_support::buffer;
using final_move_support::copies;

static int failures = 0;

static void check(bool ok, const char *what) {
  if (!ok) {
    std::cerr << "FAIL: " << what << "\n";
    ++failures;
  }
}

int main() {
  {
    buffer b;
    b.items = {5};
    copies() = 0;
    auto [b2, n] = T::thread_end(std::move(b), 3);
    check(n == 6, "thread_end sum");
    check(b2.items.size() == 2 && b2.items[1] == 7, "thread_end buffer");
    check(copies() == 0, "thread_end moves the buffer at its last use");
  }
  {
    buffer b;
    b.items = {5};
    copies() = 0;
    auto [b2, n] = T::thread_both(std::move(b), 3);
    check(n == 6 + 3, "thread_both reads the original buffer after the call");
    check(b2.items.size() == 2 && b2.items[1] == 7, "thread_both buffer");
  }
  {
    buffer b;
    b.items = {5};
    auto t = Tree::node(Tree::leaf(1), Tree::node(Tree::leaf(2), Tree::leaf(3)));
    auto bs = T::thread_tree(std::move(b), t);
    uint64_t sum = 0, leaves = 0;
    while (std::holds_alternative<typename List<buffer>::Cons>(bs.v())) {
      const auto &[x, rest] = std::get<typename List<buffer>::Cons>(bs.v());
      check(x.items.size() == 2 && x.items[0] == 5, "thread_tree leaf buffer");
      sum += x.items[1];
      ++leaves;
      List<buffer> next = *rest;
      bs = next;
    }
    check(leaves == 3 && sum == 6, "thread_tree visits every leaf");
  }
  if (failures) return 1;
  std::cout << "loopify_final_move: ok\n";
  return 0;
}
