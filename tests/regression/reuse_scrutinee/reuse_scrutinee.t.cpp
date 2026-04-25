#include <reuse_scrutinee.h>

#include <cassert>
#include <iostream>

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

int main() {
  using RS = ReuseScrutinee;

  // Verify expected_sum works correctly
  auto es = RS::expected_sum;
  std::cout << "expected_sum = " << es << std::endl;
  assert(es == 40u);

  // reuse_bug: if reuse optimization fires, subtree_sum(t)
  // accesses t's subtrees after they've been moved out → crash
  auto rb = RS::reuse_bug;
  std::cout << "reuse_bug = " << rb << std::endl;
  assert(rb == 40u);

  // reuse_direct: tail constructor Node Leaf (subtree_sum t) r
  // If reuse fires, subtree_sum(t) sees null subtrees
  auto rd = RS::reuse_direct;
  std::cout << "reuse_direct = ";
  std::visit(
      Overloaded{
          [](const RS::tree::Leaf) { std::cout << "Leaf"; },
          [](const RS::tree::Node &n) {
            std::cout << "Node(_, " << n.d_a1 << ", _)";
          }},
      rd.v());
  std::cout << std::endl;

  std::cout << "All reuse_scrutinee tests passed!" << std::endl;
  return 0;
}
