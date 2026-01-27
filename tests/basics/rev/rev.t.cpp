// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "rev.h"

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
template<typename T>
std::vector<T> list_to_vector(const std::shared_ptr<List::list<T>>& l) {
  std::vector<T> result;
  auto current = l;
  while (true) {
    bool done = false;
    std::visit(
      Overloaded{
        [&](const typename List::list<T>::nil&) {
          done = true;
        },
        [&](const typename List::list<T>::cons& c) {
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
template<typename T>
std::shared_ptr<List::list<T>> vector_to_list(const std::vector<T>& vec) {
  auto result = List::list<T>::ctor::nil_();
  for (auto it = vec.rbegin(); it != vec.rend(); ++it) {
    result = List::list<T>::ctor::cons_(*it, result);
  }
  return result;
}

int main() {
  // Test 1: Reverse empty list
  {
    auto empty = List::list<unsigned int>::ctor::nil_();
    auto result = better_rev<unsigned int>(empty);
    auto vec = list_to_vector(result);
    ASSERT(vec.size() == 0);
    std::cout << "Test 1 (reverse empty list): PASSED" << std::endl;
  }

  // Test 2: Reverse single element
  {
    auto single = List::list<unsigned int>::ctor::cons_(42, List::list<unsigned int>::ctor::nil_());
    auto result = better_rev<unsigned int>(single);
    auto vec = list_to_vector(result);
    ASSERT(vec.size() == 1);
    ASSERT(vec[0] == 42);
    std::cout << "Test 2 (reverse single element): PASSED" << std::endl;
  }

  // Test 3: Reverse two elements
  {
    auto input = vector_to_list<unsigned int>({1, 2});
    auto result = better_rev<unsigned int>(input);
    auto vec = list_to_vector(result);
    ASSERT(vec.size() == 2);
    ASSERT(vec[0] == 2 && vec[1] == 1);
    std::cout << "Test 3 (reverse two elements): PASSED" << std::endl;
  }

  // Test 4: Reverse longer list
  {
    auto input = vector_to_list<unsigned int>({1, 2, 3, 4, 5});
    auto result = better_rev<unsigned int>(input);
    auto vec = list_to_vector(result);
    ASSERT(vec.size() == 5);
    ASSERT(vec[0] == 5 && vec[1] == 4 && vec[2] == 3 && vec[3] == 2 && vec[4] == 1);
    std::cout << "Test 4 (reverse longer list): PASSED" << std::endl;
  }

  // Test 5: Double reverse should give original
  {
    auto input = vector_to_list<unsigned int>({3, 1, 4, 1, 5});
    auto reversed = better_rev<unsigned int>(input);
    auto double_reversed = better_rev<unsigned int>(reversed);
    auto vec1 = list_to_vector(input);
    auto vec2 = list_to_vector(double_reversed);
    ASSERT(vec1 == vec2);
    std::cout << "Test 5 (double reverse): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll reverse tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
