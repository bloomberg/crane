#include <loopify_operand_match_call.h>

#include <cassert>
#include <cstdint>

using M = LoopifyOperandMatchCall;

static void check(uint64_t n, uint64_t depth, uint64_t mirrored_size, uint64_t mirrored_depth, uint64_t twice_size) {
  auto t = M::comb(n);
  auto m = M::mirror(t);
  assert(M::depthish(t) == depth);
  assert(M::size(m) == mirrored_size);
  assert(M::depthish(m) == mirrored_depth);
  assert(M::size(M::mirror(m)) == twice_size);
}

// A right spine [depth] nodes deep: [depthish] recurses down its right
// children, [mirror] makes it a left spine, down which [depthish] recurses
// again.  Run on the C++ stack, either overflows it.
static void deep(uint64_t depth) {
  auto t = M::tree::leaf();
  for (uint64_t i = 0; i < depth; i++)
    t = M::tree::node(M::tree::leaf(), std::move(t));
  assert(M::depthish(t) == depth);
  auto m = M::mirror(t);
  assert(M::depthish(m) == depth);
  assert(M::size(m) == depth + 1);
}

int main() {
  check(0, 0, 1, 0, 1);
  check(5, 19, 20, 19, 32);
  check(10, 231, 232, 231, 1024);
  check(21, 46366, 46367, 46366, 2097152);
  deep(100000);
  return 0;
}
