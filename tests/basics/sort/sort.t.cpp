// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "sort.h"

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>
#include <vector>

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

// Helper to convert list to vector for testing
std::vector<unsigned int>
list_to_vector(const std::shared_ptr<List<unsigned int>> &l) {
  std::vector<unsigned int> result;
  auto current = l;
  while (true) {
    bool done = false;
    std::visit(Overloaded{[&](const typename List<unsigned int>::Nil &) {
                            done = true;
                          },
                          [&](const typename List<unsigned int>::Cons &c) {
                            result.push_back(c.d_a0);
                            current = c.d_a1;
                          }},
               current->v());
    if (done)
      break;
  }
  return result;
}

// Helper to create a list from a vector
std::shared_ptr<List<unsigned int>>
vector_to_list(const std::vector<unsigned int> &vec) {
  auto result = List<unsigned int>::nil();
  for (auto it = vec.rbegin(); it != vec.rend(); ++it) {
    result = List<unsigned int>::cons(*it, result);
  }
  return result;
}

// Generic sort test: runs a sort function on various inputs and checks results
template <typename SortFn>
void test_sort(const std::string &name, SortFn sortFn) {
  std::cout << "Testing " << name << "..." << std::endl;

  // Empty list
  {
    auto empty = List<unsigned int>::nil();
    auto result = sortFn(empty);
    auto sorted_list = std::get<0>(result->v()).d_x;
    auto vec = list_to_vector(sorted_list);
    ASSERT(vec.size() == 0);
  }

  // Single element
  {
    auto single =
        List<unsigned int>::cons(5, List<unsigned int>::nil());
    auto result = sortFn(single);
    auto sorted_list = std::get<0>(result->v()).d_x;
    auto vec = list_to_vector(sorted_list);
    ASSERT(vec.size() == 1);
    ASSERT(vec[0] == 5);
  }

  // Two elements
  {
    auto input = vector_to_list({2, 1});
    auto result = sortFn(input);
    auto sorted_list = std::get<0>(result->v()).d_x;
    auto vec = list_to_vector(sorted_list);
    ASSERT(vec.size() == 2);
    ASSERT(vec[0] == 1 && vec[1] == 2);
  }

  // Already sorted
  {
    auto input = vector_to_list({1, 2, 3, 4, 5, 6, 7, 8});
    auto result = sortFn(input);
    auto sorted_list = std::get<0>(result->v()).d_x;
    auto vec = list_to_vector(sorted_list);
    ASSERT(vec.size() == 8);
    for (size_t i = 0; i < 8; ++i) {
      ASSERT(vec[i] == i + 1);
    }
  }

  // Reverse sorted
  {
    auto input = vector_to_list({8, 7, 6, 5, 4, 3, 2, 1});
    auto result = sortFn(input);
    auto sorted_list = std::get<0>(result->v()).d_x;
    auto vec = list_to_vector(sorted_list);
    ASSERT(vec.size() == 8);
    for (size_t i = 0; i < 8; ++i) {
      ASSERT(vec[i] == i + 1);
    }
  }

  // Unsorted with duplicates
  {
    auto input = vector_to_list({5, 2, 8, 1, 9, 3, 7, 4, 6, 5});
    auto result = sortFn(input);
    auto sorted_list = std::get<0>(result->v()).d_x;
    auto vec = list_to_vector(sorted_list);
    ASSERT(vec.size() == 10);
    for (size_t i = 1; i < vec.size(); ++i) {
      ASSERT(vec[i - 1] <= vec[i]);
    }
  }

  std::cout << "  " << name << ": PASSED" << std::endl;
}

int main() {
  test_sort("insertion sort", Sort::isort);
  test_sort("merge sort", Sort::msort);
  test_sort("pair sort", Sort::psort);
  test_sort("quick sort", Sort::qsort);

  if (testStatus == 0) {
    std::cout << "\nAll sort tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
