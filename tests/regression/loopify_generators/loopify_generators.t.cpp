// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_generators.h>

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
  using List = ::List<unsigned int>;

  // Test cycle
  auto l = List::cons(1u, List::cons(2u, List::nil()));
  auto cycled = LoopifyGenerators::cycle(3u, l);
  ASSERT(cycled != nullptr);

  // Test iterate
  auto inc = [](unsigned int x) { return x + 1; };
  auto iterated = LoopifyGenerators::iterate(inc, 5u, 10u);
  ASSERT(iterated != nullptr);

  // Test zip_with
  auto l1 = List::cons(
      1u, List::cons(2u, List::cons(3u, List::nil())));
  auto l2 = List::cons(
      4u, List::cons(5u, List::cons(6u, List::nil())));
  auto add = [](unsigned int x, unsigned int y) { return x + y; };
  auto zipped = LoopifyGenerators::zip_with(add, l1, l2);
  ASSERT(zipped != nullptr);

  // Test zip_longest
  auto l3 = List::cons(1u, List::cons(2u, List::nil()));
  auto l4 = List::cons(
      3u, List::cons(4u, List::cons(5u, List::nil())));
  auto zipped_long = LoopifyGenerators::zip_longest(l3, l4, 0u);
  ASSERT(zipped_long != nullptr);

  std::cout << "All generator tests passed!\n";
  return testStatus;
}
