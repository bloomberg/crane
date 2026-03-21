// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_option_maybe.h>

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

  // find_even
  auto fe = LoopifyOptionMaybe::find_even(l5);
  ASSERT(fe && *fe == 2u);

  // find_greater
  auto fg = LoopifyOptionMaybe::find_greater(3u, l5);
  ASSERT(fg && *fg == 4u);

  // lookup
  using PairList = List<std::pair<unsigned int, unsigned int>>;
  auto pair_nil = PairList::ctor::Nil_();
  auto pairs = PairList::ctor::Cons_(std::make_pair(1u, 10u),
    PairList::ctor::Cons_(std::make_pair(2u, 20u), pair_nil));
  auto found = LoopifyOptionMaybe::lookup(2u, pairs);
  ASSERT(found && *found == 20u);

  // lookup_all
  auto pairs_dup = PairList::ctor::Cons_(std::make_pair(1u, 10u),
    PairList::ctor::Cons_(std::make_pair(1u, 11u), pair_nil));
  auto all_vals = LoopifyOptionMaybe::lookup_all(1u, pairs_dup);
  ASSERT(all_vals != nullptr);

  // safe_head
  auto sh = LoopifyOptionMaybe::safe_head(l5);
  ASSERT(sh && *sh == 1u);

  // safe_tail
  auto st = LoopifyOptionMaybe::safe_tail(l5);
  ASSERT(st);

  // catMaybes
  using OptList = List<std::optional<unsigned int>>;
  auto opt_nil = OptList::ctor::Nil_();
  auto opts = OptList::ctor::Cons_(std::make_optional(1u),
    OptList::ctor::Cons_(std::optional<unsigned int>(),
      OptList::ctor::Cons_(std::make_optional(3u), opt_nil)));
  auto catted = LoopifyOptionMaybe::catMaybes(opts);
  ASSERT(catted != nullptr);

  // find_index_even
  auto fie = LoopifyOptionMaybe::find_index_even(l5);
  ASSERT(fie && *fie == 1u);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
