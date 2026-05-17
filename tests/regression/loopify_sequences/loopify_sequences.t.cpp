// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_sequences.h>

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

  // Test alternate_sum
  auto lst = List::cons(
      UINT64_C(1), List::cons(UINT64_C(2), List::cons(UINT64_C(3), List::nil())));
  auto alt = LoopifySequences::alternate_sum(UINT64_C(1), UINT64_C(0), lst);
  ASSERT(alt == UINT64_C(3)); // 0 + 1 - 2 + 3 = 3 (saturating sub: 1-2=0, then 0+3=3)

  // Test join_with
  auto joined = LoopifySequences::join_with(UINT64_C(0), lst);

  // Test collatz_list
  auto coll = LoopifySequences::collatz_list(UINT64_C(10));
  ASSERT(std::holds_alternative<List::Cons>(coll.v()));

  // Test run_sum
  auto running = LoopifySequences::run_sum(lst);
  ASSERT(std::holds_alternative<List::Cons>(running.v()));
  ASSERT(std::get<List::Cons>(running.v()).a0 == UINT64_C(0));

  // Test intercalate
  using ListList = ::List<::List<uint64_t>>;
  auto l1 = List::cons(UINT64_C(1), List::cons(UINT64_C(2), List::nil()));
  auto l2 = List::cons(UINT64_C(3), List::cons(UINT64_C(4), List::nil()));
  auto sep = List::cons(UINT64_C(0), List::nil());
  auto lists = ListList::cons(
      l1, ListList::cons(l2, ListList::nil()));
  auto inter = LoopifySequences::intercalate(sep, lists);

  std::cout << "All sequence tests passed!\n";
  return testStatus;
}
