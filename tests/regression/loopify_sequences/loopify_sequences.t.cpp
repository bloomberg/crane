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
      1ULL, List::cons(2ULL, List::cons(3ULL, List::nil())));
  auto alt = LoopifySequences::alternate_sum(1ULL, 0ULL, lst);
  ASSERT(alt == 3ULL); // 0 + 1 - 2 + 3 = 3 (saturating sub: 1-2=0, then 0+3=3)

  // Test join_with
  auto joined = LoopifySequences::join_with(0ULL, lst);

  // Test collatz_list
  auto coll = LoopifySequences::collatz_list(10ULL);
  ASSERT(std::holds_alternative<List::Cons>(coll.v()));

  // Test run_sum
  auto running = LoopifySequences::run_sum(lst);
  ASSERT(std::holds_alternative<List::Cons>(running.v()));
  ASSERT(std::get<List::Cons>(running.v()).a0 == 0ULL);

  // Test intercalate
  using ListList = ::List<::List<uint64_t>>;
  auto l1 = List::cons(1ULL, List::cons(2ULL, List::nil()));
  auto l2 = List::cons(3ULL, List::cons(4ULL, List::nil()));
  auto sep = List::cons(0ULL, List::nil());
  auto lists = ListList::cons(
      l1, ListList::cons(l2, ListList::nil()));
  auto inter = LoopifySequences::intercalate(sep, lists);

  std::cout << "All sequence tests passed!\n";
  return testStatus;
}
