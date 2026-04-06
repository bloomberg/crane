#include <deep_map.h>

#include <cassert>
#include <iostream>

int main() {
  // Build a maximally-unbalanced tree (right spine of 10k nodes).
  // Construction is loopified.
  auto t = DeepMap::build_right(10000u, DeepMap::tree<unsigned int>::leaf());
  std::cout << "Built tree with 10k nodes" << std::endl;

  auto r = DeepMap::root_or_zero(t);
  std::cout << "root = " << r << std::endl;

  // tmap is recursive. For a right-spine tree of depth 10k, the
  // recursive calls on the right child reach depth 10k.
  // Even if map succeeds, the resulting tree has the same deep shape,
  // causing a stack overflow in the destructor chain.
  auto t2 = DeepMap::map_inc(t);
  std::cout << "Mapped tree" << std::endl;

  auto r2 = DeepMap::root_or_zero(t2);
  std::cout << "root after map = " << r2 << std::endl;
  assert(r2 == r + 1u);

  // Dropping t2 triggers deep destructor chain
  t2.reset();
  std::cout << "Dropped mapped tree" << std::endl;

  t.reset();
  std::cout << "Dropped original tree" << std::endl;

  return 0;
}
