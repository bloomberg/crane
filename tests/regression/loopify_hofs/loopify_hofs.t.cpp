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
  using List = ::List<uint64_t>;

  // Test foldl1
  auto lst = List::cons(
      UINT64_C(1), List::cons(UINT64_C(2), List::cons(UINT64_C(3), List::nil())));
  auto sum = [](uint64_t a, uint64_t b) { return a + b; };
  ASSERT(LoopifyHofs::foldl1(sum, UINT64_C(0), lst) == UINT64_C(6));

  // Test forall_
  auto gt0 = [](uint64_t x) { return x > 0; };
  ASSERT(LoopifyHofs::forall_(gt0, lst));
  auto gt5 = [](uint64_t x) { return x > 5; };
  ASSERT(!LoopifyHofs::forall_(gt5, lst));

  // Test exists_fn
  ASSERT(LoopifyHofs::exists_fn(gt5, List::cons(UINT64_C(6), lst)) == true);
  ASSERT(LoopifyHofs::exists_fn(gt5, lst) == false);

  // Test drop_while
  auto lt3 = [](uint64_t x) { return x < 3; };
  auto dropped = LoopifyHofs::drop_while(lt3, lst);
  ASSERT(std::get<List::Cons>(dropped.v()).a0 == UINT64_C(3));

  // Test take_while
  auto taken = LoopifyHofs::take_while(lt3, lst);

  // Test all_pairs
  auto lst2a = List::cons(UINT64_C(1), List::cons(UINT64_C(2), List::nil()));
  auto lst2b = List::cons(UINT64_C(3), List::cons(UINT64_C(4), List::nil()));
  auto pairs = LoopifyHofs::all_pairs(lst2a, lst2b);

  // Test find_indices
  auto eq2 = [](uint64_t x) { return x == 2; };
  auto lst3 = List::cons(
      UINT64_C(1), List::cons(
              UINT64_C(2), List::cons(
                      UINT64_C(2), List::cons(UINT64_C(3), List::nil()))));
  auto indices = LoopifyHofs::find_indices(eq2, lst3);

  // Test delete_by
  auto eq = [](uint64_t x, uint64_t y) { return x == y; };
  auto deleted = LoopifyHofs::delete_by(eq, UINT64_C(2), lst);

  // Test is_prefix_of
  auto prefix =
      List::cons(UINT64_C(1), List::cons(UINT64_C(2), List::nil()));
  ASSERT(LoopifyHofs::is_prefix_of(prefix, lst));
  auto not_prefix =
      List::cons(UINT64_C(2), List::cons(UINT64_C(3), List::nil()));
  ASSERT(!LoopifyHofs::is_prefix_of(not_prefix, lst));

  // Test lookup_all: [(1,10), (2,20), (1,30)] lookup 1 -> [10,30]
  using PairList = ::List<std::pair<uint64_t, uint64_t>>;
  auto assoc = PairList::cons(
      std::make_pair(UINT64_C(1), UINT64_C(10)),
      PairList::cons(std::make_pair(UINT64_C(2), UINT64_C(20)),
                            PairList::cons(std::make_pair(UINT64_C(1), UINT64_C(30)),
                                                  PairList::nil())));
  auto values = LoopifyHofs::lookup_all(UINT64_C(1), assoc);

  std::cout << "All HOF tests passed!\n";
  return testStatus;
}
