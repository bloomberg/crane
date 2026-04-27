// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_strings.h>

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
  auto abc = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(3u, nil)));
  auto sep = UIntList::cons(0u, nil);

  // join_with
  auto joined = LoopifyStrings::join_with(0u, abc);
  // [1, 0, 2, 0, 3]

  // repeat_string
  auto repeated = LoopifyStrings::repeat_string(abc, 3u);

  // repeat_with_sep
  auto rep_sep = LoopifyStrings::repeat_with_sep(abc, sep, 3u);

  // is_palindrome
  auto pal = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(1u, nil)));
  ASSERT(LoopifyStrings::is_palindrome(pal) == true);
  ASSERT(LoopifyStrings::is_palindrome(abc) == false);

  // intersperse
  auto inter = LoopifyStrings::intersperse(0u, abc);

  // intercalate
  using UIntListList = List<List<unsigned int>>;
  auto ll_nil = UIntListList::nil();
  auto ll = UIntListList::cons(abc,
    UIntListList::cons(abc, ll_nil));
  auto intercal = LoopifyStrings::intercalate(sep, ll);

  // replicate
  auto reps = LoopifyStrings::replicate(5u, 7u);

  // run_length_encode
  auto dups = UIntList::cons(1u, UIntList::cons(1u, UIntList::cons(
    2u, UIntList::cons(2u, UIntList::cons(2u, UIntList::cons(3u, nil))))));
  auto encoded = LoopifyStrings::run_length_encode(dups);
  // [(1,2), (2,3), (3,1)]
  using PairList = List<std::pair<unsigned int, unsigned int>>;

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
