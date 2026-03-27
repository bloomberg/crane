// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_structures.h>

namespace {
int testStatus = 0;
void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100)
      ++testStatus;
  }
}
} // namespace
#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  using NestedList =
      ::List<std::shared_ptr<LoopifyStructures::nested>>;

  // Test nested structure
  auto elem1 = LoopifyStructures::nested::elem(5u);
  auto elem2 = LoopifyStructures::nested::elem(3u);
  auto inner_list = NestedList::cons(
      elem1, NestedList::cons(elem2, NestedList::nil()));
  auto nested = LoopifyStructures::nested::nlist(inner_list);

  ASSERT(nested->nested_sum() == 8u); // 5 + 3

  auto elem_only = LoopifyStructures::nested::elem(10u);
  ASSERT(elem_only->nested_sum() == 10u);

  // Test nested_depth
  ASSERT(nested->nested_depth() >= 0u);

  // Test nested_flatten
  auto flattened = nested->nested_flatten();
  ASSERT(flattened != nullptr);

  // Test quadtree
  auto leaf1 = LoopifyStructures::quadtree::qleaf(1u);
  auto leaf2 = LoopifyStructures::quadtree::qleaf(2u);
  auto leaf3 = LoopifyStructures::quadtree::qleaf(3u);
  auto leaf4 = LoopifyStructures::quadtree::qleaf(4u);
  auto quad =
      LoopifyStructures::quadtree::quad(leaf1, leaf2, leaf3, leaf4);

  ASSERT(quad->quad_sum() == 10u); // 1+2+3+4

  // Test quad_depth
  ASSERT(leaf1->quad_depth() == 0u);
  ASSERT(quad->quad_depth() == 1u);

  // Test quad_map
  auto doubled =
      quad->quad_map([](unsigned int x) { return x * 2; });
  ASSERT(doubled->quad_sum() == 20u); // 2+4+6+8

  std::cout << "All structure tests passed!\n";
  return testStatus;
}
