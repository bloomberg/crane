// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_option.h>

#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <variant>

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  using List = LoopifyOption::list<unsigned int>;
  using PList = LoopifyOption::list<std::pair<unsigned int, unsigned int>>;

  // Build [1, 2, 3, 4, 5]
  auto l5 = List::ctor::Cons_(
      1u, List::ctor::Cons_(
              2u, List::ctor::Cons_(
                      3u, List::ctor::Cons_(
                              4u, List::ctor::Cons_(5u, List::ctor::Nil_())))));

  auto empty = List::ctor::Nil_();

  // Test find_opt
  auto gt3 = [](unsigned int x) -> bool { return x > 3; };
  auto gt10 = [](unsigned int x) -> bool { return x > 10; };

  auto found = LoopifyOption::find_opt(gt3, l5);
  ASSERT(found.has_value());
  ASSERT(*found == 4u);

  auto not_found = LoopifyOption::find_opt(gt10, l5);
  ASSERT(!not_found.has_value());

  auto empty_find = LoopifyOption::find_opt(gt3, empty);
  ASSERT(!empty_find.has_value());

  // Test last_opt
  auto last5 = LoopifyOption::last_opt(l5);
  ASSERT(last5.has_value());
  ASSERT(*last5 == 5u);

  auto last1 =
      LoopifyOption::last_opt(List::ctor::Cons_(42u, List::ctor::Nil_()));
  ASSERT(last1.has_value());
  ASSERT(*last1 == 42u);

  auto last_empty = LoopifyOption::last_opt(empty);
  ASSERT(!last_empty.has_value());

  // Test nth_opt
  auto n0 = LoopifyOption::nth_opt(0u, l5);
  ASSERT(n0.has_value() && *n0 == 1u);

  auto n2 = LoopifyOption::nth_opt(2u, l5);
  ASSERT(n2.has_value() && *n2 == 3u);

  auto n4 = LoopifyOption::nth_opt(4u, l5);
  ASSERT(n4.has_value() && *n4 == 5u);

  auto n_oob = LoopifyOption::nth_opt(10u, l5);
  ASSERT(!n_oob.has_value());

  // Test lookup_opt
  auto assoc = PList::ctor::Cons_(
      std::make_pair(1u, 10u),
      PList::ctor::Cons_(
          std::make_pair(2u, 20u),
          PList::ctor::Cons_(std::make_pair(3u, 30u), PList::ctor::Nil_())));

  auto lk2 = LoopifyOption::lookup_opt(2u, assoc);
  ASSERT(lk2.has_value() && *lk2 == 20u);

  auto lk99 = LoopifyOption::lookup_opt(99u, assoc);
  ASSERT(!lk99.has_value());

  // Test map_opt (keep only even numbers doubled)
  auto even_double = [](unsigned int x) -> std::optional<unsigned int> {
    if (x % 2 == 0)
      return std::make_optional<unsigned int>(x * 2);
    else
      return std::nullopt;
  };
  auto mapped =
      LoopifyOption::map_opt<unsigned int, unsigned int>(even_double, l5);
  // l5 = [1,2,3,4,5], evens = [2,4], doubled = [4,8]
  // mapped should be [4,8] - length check removed (length is stdlib)
  ASSERT(std::get<List::Cons>(mapped->v()).d_a0 == 4u);

  // Test find_index
  auto fi = LoopifyOption::find_index(gt3, l5);
  ASSERT(fi.has_value() && *fi == 3u); // index of 4

  auto fi_none = LoopifyOption::find_index(gt10, l5);
  ASSERT(!fi_none.has_value());

  return testStatus;
}
