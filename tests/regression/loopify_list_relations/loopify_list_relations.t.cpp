// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_list_relations.h>

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

int main() {
  auto nil = UIntList::nil();
  auto l3 = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(3u, nil)));
  auto l5 = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(
    3u, UIntList::cons(4u, UIntList::cons(5u, nil)))));

  // is_prefix_of
  ASSERT(LoopifyListRelations::is_prefix_of(nil, l5) == true);
  ASSERT(LoopifyListRelations::is_prefix_of(l3, l5) == true);
  ASSERT(LoopifyListRelations::is_prefix_of(l5, l3) == false);

  // is_suffix_of
  auto suffix = UIntList::cons(4u, UIntList::cons(5u, nil));
  ASSERT(LoopifyListRelations::is_suffix_of(suffix, l5) == true);

  // is_infix_of
  auto infix = UIntList::cons(2u, UIntList::cons(3u, nil));
  ASSERT(LoopifyListRelations::is_infix_of(infix, l5) == true);

  // list_eq
  ASSERT(LoopifyListRelations::list_eq(l3, l3) == true);
  ASSERT(LoopifyListRelations::list_eq(l3, l5) == false);

  // list_compare
  ASSERT(LoopifyListRelations::list_compare(l3, l3) == 0u);
  ASSERT(LoopifyListRelations::list_compare(l3, l5) == 1u);
  ASSERT(LoopifyListRelations::list_compare(l5, l3) == 2u);

  // zip
  auto zipped = LoopifyListRelations::zip(l3, l3);

  // zip3
  auto zipped3 = LoopifyListRelations::zip3(l3, l3, l3);

  // interleave
  auto inter = LoopifyListRelations::interleave(l3, l3);

  // merge
  auto merged = LoopifyListRelations::merge(l3, l3);

  // union
  auto un = LoopifyListRelations::union_(l3, l3);

  // intersection
  auto inter2 = LoopifyListRelations::intersection(l3, l5);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
