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

  // A list assigned the children of its own sole element: the cell that
  // element is boxed in is released by the assignment, after the children
  // are taken.
  using Kids = crane::list<crane::box<M::rose>>;
  auto node = [](const Kids &l) -> const M::rose::Node & {
    return std::get<M::rose::Node>(l.front().get().v());
  };
  Kids leaf = Kids::cons(M::rose::node(4, Kids{}), Kids{});
  Kids kids = Kids::cons(M::rose::node(3, std::move(leaf)), Kids{});
  kids = node(kids).kids;
  assert(!kids.empty() && node(kids).n == 4);
  Kids moved = Kids::cons(M::rose::node(5, Kids::cons(M::rose::node(6, Kids{}), Kids{})), Kids{});
  moved = std::move(const_cast<Kids &>(node(moved).kids));
  assert(!moved.empty() && node(moved).n == 6);
  return 0;
}
