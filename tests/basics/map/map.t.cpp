// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "map.h"

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
  // Test 1: Map over empty list
  {
    auto empty = List::list<unsigned int>::ctor::nil_();
    auto result = better_map<unsigned int, unsigned int>([](unsigned int x) { return x + 1; }, empty);
    auto vec = list_to_vector(result);
    ASSERT(vec.size() == 0);
    std::cout << "Test 1 (map over empty list): PASSED" << std::endl;
  }

  // Test 2: Map increment over single element
  {
    auto single = List::list<unsigned int>::ctor::cons_(42, List::list<unsigned int>::ctor::nil_());
    auto result = better_map<unsigned int, unsigned int>([](unsigned int x) { return x + 1; }, single);
    auto vec = list_to_vector(result);
    ASSERT(vec.size() == 1);
    ASSERT(vec[0] == 43);
    std::cout << "Test 2 (map increment single element): PASSED" << std::endl;
  }

  // Test 3: Map double over list
  {
    auto input = vector_to_list<unsigned int>({1, 2, 3, 4, 5});
    auto result = better_map<unsigned int, unsigned int>([](unsigned int x) { return x * 2; }, input);
    auto vec = list_to_vector(result);
    ASSERT(vec.size() == 5);
    ASSERT(vec[0] == 2 && vec[1] == 4 && vec[2] == 6 && vec[3] == 8 && vec[4] == 10);
    std::cout << "Test 3 (map double): PASSED" << std::endl;
  }

  // Test 4: Map with type change (unsigned int to bool)
  {
    auto input = vector_to_list<unsigned int>({0, 1, 2, 0, 3});
    auto result = better_map<unsigned int, bool>([](unsigned int x) { return x != 0; }, input);
    auto vec = list_to_vector(result);
    ASSERT(vec.size() == 5);
    ASSERT(vec[0] == false && vec[1] == true && vec[2] == true && vec[3] == false && vec[4] == true);
    std::cout << "Test 4 (map with type change): PASSED" << std::endl;
  }

  // Test 5: Map identity should preserve list
  {
    auto input = vector_to_list<unsigned int>({3, 1, 4, 1, 5, 9, 2, 6});
    auto result = better_map<unsigned int, unsigned int>([](unsigned int x) { return x; }, input);
    auto vec1 = list_to_vector(input);
    auto vec2 = list_to_vector(result);
    ASSERT(vec1 == vec2);
    std::cout << "Test 5 (map identity): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll map tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
