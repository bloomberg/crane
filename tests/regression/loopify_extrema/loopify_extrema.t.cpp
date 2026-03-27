// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_extrema.h>

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
  auto l5 = UIntList::cons(3u, UIntList::cons(1u, UIntList::cons(
    4u, UIntList::cons(1u, UIntList::cons(5u, nil)))));

  // maximum
  ASSERT(LoopifyExtrema::maximum(nil) == 0u);
  ASSERT(LoopifyExtrema::maximum(l5) == 5u);

  // minimum
  ASSERT(LoopifyExtrema::minimum(nil) == 0u);
  ASSERT(LoopifyExtrema::minimum(l5) == 1u);

  // minmax
  auto mm = LoopifyExtrema::minmax(l5);
  ASSERT(mm.first == 1u);   // min
  ASSERT(mm.second == 5u);  // max

  // max_by
  auto neg = [](unsigned int x) { return 100u - x; };
  ASSERT(LoopifyExtrema::max_by(neg, l5) == 99u);  // max(100-3, 100-1, 100-4, 100-1, 100-5) = 99

  // min_by
  auto id = [](unsigned int x) { return x; };
  ASSERT(LoopifyExtrema::min_by(id, l5) == 1u);

  // argmax
  ASSERT(LoopifyExtrema::argmax(id, l5) == 5u);  // element with max value

  // argmin
  ASSERT(LoopifyExtrema::argmin(id, l5) == 1u);  // element with min value

  // lex_compare
  auto l1 = UIntList::cons(1u, UIntList::cons(2u, nil));
  auto l2 = UIntList::cons(1u, UIntList::cons(3u, nil));
  ASSERT(LoopifyExtrema::lex_compare(l1, l2) == 1u);  // l1 < l2
  ASSERT(LoopifyExtrema::lex_compare(l2, l1) == 2u);  // l2 > l1
  ASSERT(LoopifyExtrema::lex_compare(l1, l1) == 0u);  // l1 == l1

  // all_equal
  auto eq = UIntList::cons(5u, UIntList::cons(5u, UIntList::cons(5u, nil)));
  ASSERT(LoopifyExtrema::all_equal(eq) == true);
  ASSERT(LoopifyExtrema::all_equal(l5) == false);

  // is_sorted
  auto sorted = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(3u, nil)));
  ASSERT(LoopifyExtrema::is_sorted(sorted) == true);
  ASSERT(LoopifyExtrema::is_sorted(l5) == false);

  // adjacent_all
  auto le = [](unsigned int x, unsigned int y) { return x <= y; };
  ASSERT(LoopifyExtrema::adjacent_all(le, sorted) == true);
  ASSERT(LoopifyExtrema::adjacent_all(le, l5) == false);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
