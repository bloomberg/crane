#include <boxed_element_container_cast.h>
#include <cassert>
#include <cstdint>
#include <vector>

using M = BoxedElementContainerCast;

int main() {
  std::vector<bool> predicates;
  for (auto l = M::predicates; !l.empty(); l = l.tail())
    predicates.push_back(l.front());
  assert((predicates == std::vector<bool>{false, true}));
  std::vector<uint64_t> sizes;
  for (auto l = M::action_sizes; !l.empty(); l = l.tail())
    sizes.push_back(l.front());
  assert((sizes == std::vector<uint64_t>{2, 100}));
  return 0;
}
