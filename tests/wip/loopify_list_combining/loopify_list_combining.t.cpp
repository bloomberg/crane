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
  auto nil = UIntList::ctor::Nil_();
  auto l3 = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(2u, UIntList::ctor::Cons_(3u, nil)));
  auto l4 = UIntList::ctor::Cons_(4u, UIntList::ctor::Cons_(5u, UIntList::ctor::Cons_(6u, nil)));

  // append
  auto appended = LoopifyListCombining::append(l3, l4);
  ASSERT(appended != nullptr);

  // intersperse
  auto inter = LoopifyListCombining::intersperse(0u, l3);
  ASSERT(inter != nullptr);

  // intercalate
  using ListList = List<std::shared_ptr<UIntList>>;
  auto ll_nil = ListList::ctor::Nil_();
  auto ll = ListList::ctor::Cons_(l3, ListList::ctor::Cons_(l4, ll_nil));
  auto sep = UIntList::ctor::Cons_(99u, nil);
  auto intercalated = LoopifyListCombining::intercalate(sep, ll);
  ASSERT(intercalated != nullptr);

  // concat
  auto concatenated = LoopifyListCombining::concat(ll);
  ASSERT(concatenated != nullptr);

  // mapcat
  auto mapcatted = LoopifyListCombining::mapcat(l3);
  ASSERT(mapcatted != nullptr);

  // interleave_two
  auto interleaved = LoopifyListCombining::interleave_two(l3, l4);
  ASSERT(interleaved != nullptr);

  // concat_sep
  auto concat_with_sep = LoopifyListCombining::concat_sep(0u, ll);
  ASSERT(concat_with_sep != nullptr);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
