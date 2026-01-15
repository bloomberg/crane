// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "isort.h"

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

void aSsErT(bool condition, const char *message, int line)
{
    if (condition) {
        std::cout << "Error " __FILE__ "(" << line << "): " << message
             << "    (failed)" << std::endl;

        if (0 <= testStatus && testStatus <= 100) {
            ++testStatus;
        }
    }
}

}  // close unnamed namespace

#define ASSERT(X)                                              \
    aSsErT(!(X), #X, __LINE__);

// Helper to convert list to vector for testing
std::vector<unsigned int> list_to_vector(const std::shared_ptr<List::list<unsigned int>>& l) {
  std::vector<unsigned int> result;
  auto current = l;
  while (true) {
    bool done = false;
    std::visit(
      Overloaded{
        [&](const typename List::list<unsigned int>::nil&) {
          done = true;
        },
        [&](const typename List::list<unsigned int>::cons& c) {
          result.push_back(c._a0);
          current = c._a1;
        }
      },
      current->v()
    );
    if (done) break;
  }
  return result;
}

// Helper to create a list from a vector
std::shared_ptr<List::list<unsigned int>> vector_to_list(const std::vector<unsigned int>& vec) {
  auto result = List::list<unsigned int>::ctor::nil_();
  for (auto it = vec.rbegin(); it != vec.rend(); ++it) {
    result = List::list<unsigned int>::ctor::cons_(*it, result);
  }
  return result;
}

int main() {
  // Test 1: Sort empty list
  {
    auto empty = List::list<unsigned int>::ctor::nil_();
    auto result = isort(empty);
    // Extract the list from the sigma type
    auto sorted_list = result->_a0;
    auto vec = list_to_vector(sorted_list);
    ASSERT(vec.size() == 0);
    std::cout << "Test 1 (empty list): PASSED" << std::endl;
  }

  // Test 2: Sort single element
  {
    auto single = List::list<unsigned int>::ctor::cons_(5, List::list<unsigned int>::ctor::nil_());
    auto result = isort(single);
    auto sorted_list = result->_a0;
    auto vec = list_to_vector(sorted_list);
    ASSERT(vec.size() == 1);
    ASSERT(vec[0] == 5);
    std::cout << "Test 2 (single element): PASSED" << std::endl;
  }

  // Test 3: Sort already sorted list
  {
    auto input = vector_to_list({1, 2, 3, 4, 5});
    auto result = isort(input);
    auto sorted_list = result->_a0;
    auto vec = list_to_vector(sorted_list);
    ASSERT(vec.size() == 5);
    ASSERT(vec[0] == 1 && vec[1] == 2 && vec[2] == 3 && vec[3] == 4 && vec[4] == 5);
    std::cout << "Test 3 (already sorted): PASSED" << std::endl;
  }

  // Test 4: Sort reverse sorted list
  {
    auto input = vector_to_list({5, 4, 3, 2, 1});
    auto result = isort(input);
    auto sorted_list = result->_a0;
    auto vec = list_to_vector(sorted_list);
    ASSERT(vec.size() == 5);
    ASSERT(vec[0] == 1 && vec[1] == 2 && vec[2] == 3 && vec[3] == 4 && vec[4] == 5);
    std::cout << "Test 4 (reverse sorted): PASSED" << std::endl;
  }

  // Test 5: Sort unsorted list
  {
    auto input = vector_to_list({3, 1, 4, 1, 5, 9, 2, 6});
    auto result = isort(input);
    auto sorted_list = result->_a0;
    auto vec = list_to_vector(sorted_list);
    ASSERT(vec.size() == 8);
    // Check sorted
    for (size_t i = 1; i < vec.size(); ++i) {
      ASSERT(vec[i-1] <= vec[i]);
    }
    std::cout << "Test 5 (unsorted list): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll insertion sort tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
