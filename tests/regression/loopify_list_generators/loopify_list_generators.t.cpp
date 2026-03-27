// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_list_generators.h>

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
using LLG = LoopifyListGenerators;

int main() {
  auto nil = UIntList::nil();
  auto l3 = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(3u, nil)));

  // cycle
  auto cycled = LLG::cycle(3u, l3);
  ASSERT(cycled != nullptr);

  // iterate
  auto double_fn = [](unsigned int x) { return x * 2; };
  auto iters = LLG::iterate(double_fn, 5u, 1u);
  // [1, 2, 4, 8, 16]
  ASSERT(iters != nullptr);

  // build_list
  auto id = [](unsigned int x) { return x; };
  auto built = LLG::build_list(5u, id);
  // [0, 1, 2, 3, 4]
  ASSERT(built != nullptr);

  // init_list
  auto square = [](unsigned int x) { return x * x; };
  auto inited = LLG::init_list(4u, square);
  // [0, 1, 4, 9]
  ASSERT(inited != nullptr);

  // range
  auto rng = LLG::range(10u, 5u);
  // [10, 11, 12, 13, 14]
  ASSERT(rng != nullptr);

  // replicate_elem
  auto reps = LLG::replicate_elem(4u, 7u);
  // [7, 7, 7, 7]
  ASSERT(reps != nullptr);

  // replicate_each
  auto rep_each = LLG::replicate_each(2u, l3);
  // [1, 1, 2, 2, 3, 3]
  ASSERT(rep_each != nullptr);

  // tabulate
  auto tab = LLG::tabulate(5u, id);
  ASSERT(tab != nullptr);

  // zip_with
  auto add = [](unsigned int x, unsigned int y) { return x + y; };
  auto zipped = LLG::zip_with(add, l3, l3);
  // [2, 4, 6]
  ASSERT(zipped != nullptr);

  // enumerate
  auto enum_list = LLG::enumerate(l3);
  // [(0,1), (1,2), (2,3)]
  ASSERT(enum_list != nullptr);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
