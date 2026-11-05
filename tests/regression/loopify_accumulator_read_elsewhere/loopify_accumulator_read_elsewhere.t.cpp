#include <loopify_accumulator_read_elsewhere.h>

#include <cassert>
#include <iostream>

int main() {
  using L = LoopifyAccumulatorReadElsewhere;

  // grow 3 leaf = node (node (node leaf 2 leaf) 1 leaf) 0 leaf
  assert(L::test_grow_size == 3u);

  // grow_counted 3 leaf 0: the accumulator doubles around a key each turn
  // (sizes 1, 3, 7) while the count adds the previous size (0, 1, 3).
  assert(L::test_counted_count == 4u);
  assert(L::test_counted_size == 7u);

  // graft walks the right spine, rebuilding the accumulator around each
  // key and its left subtree: keys 2, 1, 3 in three nodes.
  assert(L::test_graft_size == 3u);
  assert(L::test_graft_keys == 6u);

  std::cout << "All loopify_accumulator_read_elsewhere tests passed!" << std::endl;
  return 0;
}
