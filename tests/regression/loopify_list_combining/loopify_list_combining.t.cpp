// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_list_combining.h>

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
  auto l4 = UIntList::cons(4u, UIntList::cons(5u, UIntList::cons(6u, nil)));

  // append
  auto appended = LoopifyListCombining::append(l3, l4);

  // intersperse
  auto inter = LoopifyListCombining::intersperse(0u, l3);

  // intercalate
  using ListList = List<List<unsigned int>>;
  auto ll_nil = ListList::nil();
  auto ll = ListList::cons(l3, ListList::cons(l4, ll_nil));
  auto sep = UIntList::cons(99u, nil);
  auto intercalated = LoopifyListCombining::intercalate(sep, ll);

  // concat
  auto concatenated = LoopifyListCombining::concat(ll);

  // mapcat
  auto mapcatted = LoopifyListCombining::mapcat(l3);

  // interleave_two
  auto interleaved = LoopifyListCombining::interleave_two(l3, l4);

  // concat_sep
  auto concat_with_sep = LoopifyListCombining::concat_sep(0u, ll);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
