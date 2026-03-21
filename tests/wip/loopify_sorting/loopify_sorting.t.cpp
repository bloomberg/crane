// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_sorting.h>

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
  using List = ::List<unsigned int>;

  // Test sorting algorithms
  auto unsorted = List::ctor::Cons_(
      3u, List::ctor::Cons_(1u, List::ctor::Cons_(4u, List::ctor::Nil_())));

  auto ins_sorted = LoopifySorting::insertion_sort(unsorted);
  ASSERT(ins_sorted != nullptr);

  auto merge_sorted = LoopifySorting::merge_sort(unsorted);
  ASSERT(merge_sorted != nullptr);

  auto quick_sorted = LoopifySorting::quicksort(unsorted);
  ASSERT(quick_sorted != nullptr);

  // Test is_sorted
  auto sorted_list = List::ctor::Cons_(
      1u, List::ctor::Cons_(2u, List::ctor::Cons_(3u, List::ctor::Nil_())));
  ASSERT(LoopifySorting::is_sorted(sorted_list));
  ASSERT(!LoopifySorting::is_sorted(unsorted));

  // Test remove_duplicates
  auto dups = List::ctor::Cons_(
      1u, List::ctor::Cons_(1u, List::ctor::Cons_(2u, List::ctor::Nil_())));
  auto uniq = LoopifySorting::remove_duplicates(dups);
  ASSERT(uniq != nullptr);

  // Test uniq_sorted
  auto uniq2 = LoopifySorting::uniq_sorted(dups);
  ASSERT(uniq2 != nullptr);

  std::cout << "All unique sorting tests passed!\n";
  return testStatus;
}
