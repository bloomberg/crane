#include <boxed_element_block_template.h>
#include <cassert>
#include <cstdint>
#include <vector>

using M = BoxedElementBlockTemplate;

int main() {
  assert(M::sample_total == 15);
  std::vector<uint64_t> leaves;
  for (auto l = M::sample_leaves; !l.empty(); l = l.tail())
    leaves.push_back(l.front());
  assert((leaves == std::vector<uint64_t>{1, 2, 3, 5}));
  return 0;
}
