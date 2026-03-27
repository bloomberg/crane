// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_hofs.h>

#include <functional>
#include <iostream>
#include <memory>
#include <variant>

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
  using List = ::List<unsigned int>;

  // Test foldl1
  auto lst = List::cons(
      1u, List::cons(2u, List::cons(3u, List::nil())));
  auto sum = [](unsigned int a, unsigned int b) { return a + b; };
  ASSERT(LoopifyHofs::foldl1(sum, 0u, lst) == 6u);

  // Test forall_
  auto gt0 = [](unsigned int x) { return x > 0; };
  ASSERT(LoopifyHofs::forall_(gt0, lst));
  auto gt5 = [](unsigned int x) { return x > 5; };
  ASSERT(!LoopifyHofs::forall_(gt5, lst));

  // Test exists_fn
  ASSERT(LoopifyHofs::exists_fn(gt5, List::cons(6u, lst)) == true);
  ASSERT(LoopifyHofs::exists_fn(gt5, lst) == false);

  // Test drop_while
  auto lt3 = [](unsigned int x) { return x < 3; };
  auto dropped = LoopifyHofs::drop_while(lt3, lst);
  ASSERT(std::get<List::Cons>(dropped->v()).d_a0 == 3u);

  // Test take_while
  auto taken = LoopifyHofs::take_while(lt3, lst);
  ASSERT(taken != nullptr);

  // Test all_pairs
  auto lst2a = List::cons(1u, List::cons(2u, List::nil()));
  auto lst2b = List::cons(3u, List::cons(4u, List::nil()));
  auto pairs = LoopifyHofs::all_pairs(lst2a, lst2b);
  ASSERT(pairs != nullptr);

  // Test find_indices
  auto eq2 = [](unsigned int x) { return x == 2; };
  auto lst3 = List::cons(
      1u, List::cons(
              2u, List::cons(
                      2u, List::cons(3u, List::nil()))));
  auto indices = LoopifyHofs::find_indices(eq2, lst3);
  ASSERT(indices != nullptr);

  // Test delete_by
  auto eq = [](unsigned int x, unsigned int y) { return x == y; };
  auto deleted = LoopifyHofs::delete_by(eq, 2u, lst);
  ASSERT(deleted != nullptr);

  // Test is_prefix_of
  auto prefix =
      List::cons(1u, List::cons(2u, List::nil()));
  ASSERT(LoopifyHofs::is_prefix_of(prefix, lst));
  auto not_prefix =
      List::cons(2u, List::cons(3u, List::nil()));
  ASSERT(!LoopifyHofs::is_prefix_of(not_prefix, lst));

  // Test lookup_all: [(1,10), (2,20), (1,30)] lookup 1 -> [10,30]
  using PairList = ::List<std::pair<unsigned int, unsigned int>>;
  auto assoc = PairList::cons(
      std::make_pair(1u, 10u),
      PairList::cons(std::make_pair(2u, 20u),
                            PairList::cons(std::make_pair(1u, 30u),
                                                  PairList::nil())));
  auto values = LoopifyHofs::lookup_all(1u, assoc);
  ASSERT(values != nullptr);

  std::cout << "All HOF tests passed!\n";
  return testStatus;
}
