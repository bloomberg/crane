// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_advanced_patterns.h>

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

using UIntList = List<unsigned int>;
using ShapeList = List<std::shared_ptr<LoopifyAdvancedPatterns::shape>>;
using TripleList = List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>;

int main() {
  auto nil = UIntList::ctor::Nil_();
  auto l3 = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(2u, UIntList::ctor::Cons_(3u, nil)));
  auto l5 = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(2u, UIntList::ctor::Cons_(
    3u, UIntList::ctor::Cons_(4u, UIntList::ctor::Cons_(5u, nil)))));

  // as_guard - keeps elements if list length > 3
  auto result1 = LoopifyAdvancedPatterns::as_guard(l5);
  // Length is 5 > 3, so all should be kept
  ASSERT(LoopifyAdvancedPatterns::len_impl(result1) == 2u);  // only first 2 elements pass guard

  auto l2 = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(2u, nil));
  auto result2 = LoopifyAdvancedPatterns::as_guard(l2);
  // Length is 2 <= 3, so all should be filtered
  ASSERT(LoopifyAdvancedPatterns::len_impl(result2) == 0u);

  // multi_guard
  auto lg = UIntList::ctor::Cons_(15u, UIntList::ctor::Cons_(5u, UIntList::ctor::Cons_(0u, nil)));
  ASSERT(LoopifyAdvancedPatterns::multi_guard(lg) == 16u);  // 15 + 0 + 1

  // four_elem
  ASSERT(LoopifyAdvancedPatterns::four_elem(nil) == 0u);
  ASSERT(LoopifyAdvancedPatterns::four_elem(l3) == 3u);
  auto l4 = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(2u, UIntList::ctor::Cons_(
    3u, UIntList::ctor::Cons_(4u, nil))));
  ASSERT(LoopifyAdvancedPatterns::four_elem(l4) == 10u);  // 1+2+3+4

  // nested_pattern - sum all elements in list of triples
  // Note: generated type is pair<pair<uint, uint>, uint> (left-nested pairs)
  auto triple_nil = TripleList::ctor::Nil_();
  auto t1 = std::make_pair(std::make_pair(1u, 2u), 3u);
  auto t2 = std::make_pair(std::make_pair(4u, 5u), 6u);
  auto triples = TripleList::ctor::Cons_(t1, TripleList::ctor::Cons_(t2, triple_nil));
  ASSERT(LoopifyAdvancedPatterns::nested_pattern(triples) == 21u);  // 1+2+3+4+5+6

  // guard_accum
  auto lacc = UIntList::ctor::Cons_(120u, UIntList::ctor::Cons_(60u, UIntList::ctor::Cons_(5u, nil)));
  ASSERT(LoopifyAdvancedPatterns::guard_accum(10u, lacc) == 81u);  // 10*2=20, +60=80, +1=81

  // cons_computed
  auto comp = LoopifyAdvancedPatterns::cons_computed(3u, l3);
  ASSERT(LoopifyAdvancedPatterns::len_impl(comp) == 3u);

  // sum_shapes
  auto c1 = LoopifyAdvancedPatterns::shape::ctor::Circle_(5u);
  auto s1 = LoopifyAdvancedPatterns::shape::ctor::Square_(3u);
  auto t_1 = LoopifyAdvancedPatterns::shape::ctor::Triangle_(2u);
  auto shapes_nil = ShapeList::ctor::Nil_();
  auto shapes = ShapeList::ctor::Cons_(c1,
    ShapeList::ctor::Cons_(s1,
    ShapeList::ctor::Cons_(t_1, shapes_nil)));
  ASSERT(LoopifyAdvancedPatterns::sum_shapes(shapes) == 10u);

  // count_by_shape
  // Returns pair<pair<uint, uint>, uint>: ((circles, squares), triangles)
  auto counts = LoopifyAdvancedPatterns::count_by_shape(shapes);
  ASSERT(counts.first.first == 1u);   // circles
  ASSERT(counts.first.second == 1u);  // squares
  ASSERT(counts.second == 1u);        // triangles

  // replace_at
  auto replaced = LoopifyAdvancedPatterns::replace_at(1u, 99u, l3);
  // Should be [1, 99, 3]
  ASSERT(LoopifyAdvancedPatterns::len_impl(replaced) == 3u);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
