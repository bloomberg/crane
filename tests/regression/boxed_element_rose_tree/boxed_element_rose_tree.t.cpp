#include <boxed_element_rose_tree.h>
#include <cassert>
#include <cstdint>
#include <vector>

using M = BoxedElementRoseTree;

int main() {
  assert(M::sample_size == 6);
  assert(M::sample_total == 21);
  std::vector<uint64_t> labels;
  for (auto l = M::sample_labels; !l.empty(); l = l.tail())
    labels.push_back(l.front());
  assert((labels == std::vector<uint64_t>{1, 2, 3, 6}));
  return 0;
}
