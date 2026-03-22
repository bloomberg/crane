// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_list_subsequences.h>

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
  auto nil = UIntList::ctor::Nil_();
  auto l5 = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(2u, UIntList::ctor::Cons_(
    3u, UIntList::ctor::Cons_(4u, UIntList::ctor::Cons_(5u, nil)))));

  // tails
  auto t = LoopifyListSubsequences::tails(l5);
  ASSERT(t != nullptr);

  // inits
  auto i = LoopifyListSubsequences::inits(l5);
  ASSERT(i != nullptr);

  // init_list
  auto init = LoopifyListSubsequences::init_list(l5);
  ASSERT(init != nullptr);

  // snoc
  auto snoced = LoopifyListSubsequences::snoc(l5, 99u);
  ASSERT(snoced != nullptr);

  // last_elem
  ASSERT(LoopifyListSubsequences::last_elem(l5) == 5u);

  // nth_elem
  ASSERT(LoopifyListSubsequences::nth_elem(2u, l5) == 3u);

  // split_at
  auto split = LoopifyListSubsequences::split_at(2u, l5);
  ASSERT(split.first != nullptr && split.second != nullptr);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
