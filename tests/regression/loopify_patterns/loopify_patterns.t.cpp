// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <functional>
#include <iostream>
#include <loopify_patterns.h>

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
  using List = LoopifyPatterns::list<unsigned int>;

  // Test multi_let
  ASSERT(LoopifyPatterns::multi_let(5u) > 0u);

  // Test nested_if
  ASSERT(LoopifyPatterns::nested_if(12u) >= 0u);

  // Test deep_nest
  ASSERT(LoopifyPatterns::deep_nest(3u) == 9u);

  // Test bool_chain
  ASSERT(LoopifyPatterns::bool_chain(5u, 3u));
  ASSERT(!LoopifyPatterns::bool_chain(5u, 10u));

  // Test chained_comp
  ASSERT(LoopifyPatterns::chained_comp(5u));

  // Test tuple_constr - returns ((a,b),c)
  auto tuple_result = LoopifyPatterns::tuple_constr(3u);
  auto a = tuple_result.first.first;
  auto b = tuple_result.first.second;
  auto c = tuple_result.second;
  ASSERT(a == 3u && b > 0u && c > 0u);

  // Test sum_prod_count - returns ((sum,prod),count)
  auto lst = List::ctor::Cons_(
      2u, List::ctor::Cons_(3u, List::ctor::Cons_(4u, List::ctor::Nil_())));
  auto spc_result = LoopifyPatterns::sum_prod_count(lst, 0u, 1u, 0u);
  auto sum = spc_result.first.first;
  auto prod = spc_result.first.second;
  auto count = spc_result.second;
  ASSERT(sum == 9u && prod == 24u && count == 3u);

  // Test split_by_sign
  auto [pos, neg] = LoopifyPatterns::split_by_sign(lst, 3u);
  ASSERT(pos != nullptr && neg != nullptr);

  // Test guard_accum
  auto result = LoopifyPatterns::guard_accum(0u, lst);
  ASSERT(result >= 0u);

  // Test mod_pattern: mod_pattern(5) = 4 mod (1 + mod_pattern(3)) = 4 mod 1 = 0
  ASSERT(LoopifyPatterns::mod_pattern(5u) == 0u);
  // mod_pattern(4) = 3 mod (1 + mod_pattern(2)) = 3 mod (1 + 1 mod 2) = 3 mod 2
  // = 1
  ASSERT(LoopifyPatterns::mod_pattern(4u) == 1u);

  // Test alternating_ops
  ASSERT(LoopifyPatterns::alternating_ops(5u) > 0u);

  // Test max_by
  auto max_result =
      LoopifyPatterns::max_by([](unsigned int x) { return x * x; }, lst);
  ASSERT(max_result == 16u); // max(4,9,16) = 16

  // Test replace_at
  auto replaced = LoopifyPatterns::replace_at(1u, 99u, lst);
  ASSERT(replaced != nullptr);

  // Test nested_pattern
  using Pair3 = std::pair<std::pair<unsigned int, unsigned int>, unsigned int>;
  using TupleList = LoopifyPatterns::list<Pair3>;
  auto tpl = TupleList::ctor::Cons_(
      std::make_pair(std::make_pair(1u, 2u), 3u),
      TupleList::ctor::Cons_(std::make_pair(std::make_pair(4u, 5u), 6u),
                             TupleList::ctor::Nil_()));
  ASSERT(LoopifyPatterns::nested_pattern(tpl) == 21u);

  // Test let_nested
  ASSERT(LoopifyPatterns::let_nested(3u) > 0u);

  std::cout << "All pattern tests passed!\n";
  return testStatus;
}
