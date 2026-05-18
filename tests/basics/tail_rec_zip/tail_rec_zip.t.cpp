// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "tail_rec_zip.h"

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <utility>
#include <variant>
#include <vector>

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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
template <typename T>
std::vector<T> list_to_vector(const List<T> &l) {
  std::vector<T> result;
  const List<T> *current = &l;
  while (true) {
    bool done = false;
    std::visit(Overloaded{[&](const typename List<T>::Nil &) { done = true; },
                          [&](const typename List<T>::Cons &c) {
                            result.push_back(c.a);
                            current = c.l.get();
                          }},
               current->v());
    if (done)
      break;
  }
  return result;
}

// Helper to create a list from a vector
template <typename T>
List<T> vector_to_list(const std::vector<T> &vec) {
  auto result = List<T>::nil();
  for (auto it = vec.rbegin(); it != vec.rend(); ++it) {
    result = List<T>::cons(*it, result);
  }
  return result;
}

// Helper to convert Prod to std::pair
template <typename A, typename B>
std::pair<A, B> prod_to_pair(const Prod<A, B> &p) {
  return std::make_pair(p.a0, p.a1);
}

// Helper to convert list of prods to vector of pairs
template <typename A, typename B>
std::vector<std::pair<A, B>>
list_to_pairs(const List<Prod<A, B>> &l) {
  auto prods = list_to_vector(l);
  std::vector<std::pair<A, B>> result;
  for (const auto &p : prods) {
    result.push_back(prod_to_pair<A, B>(p));
  }
  return result;
}

int main() {
  // Test 1: Zip empty lists
  {
    auto empty_a = List<uint64_t>::nil();
    auto empty_b = List<uint64_t>::nil();
    auto result = better_zip<uint64_t, uint64_t>(empty_a, empty_b);
    auto vec = list_to_pairs<uint64_t, uint64_t>(result);
    ASSERT(vec.size() == 0);
    std::cout << "Test 1 (zip empty lists): PASSED" << std::endl;
  }

  // Test 2: Zip single elements
  {
    auto a =
        List<uint64_t>::cons(1, List<uint64_t>::nil());
    auto b =
        List<uint64_t>::cons(2, List<uint64_t>::nil());
    auto result = better_zip<uint64_t, uint64_t>(a, b);
    auto vec = list_to_pairs<uint64_t, uint64_t>(result);
    ASSERT(vec.size() == 1);
    ASSERT(vec[0].first == 1 && vec[0].second == 2);
    std::cout << "Test 2 (zip single elements): PASSED" << std::endl;
  }

  // Test 3: Zip equal length lists
  {
    auto a = vector_to_list<uint64_t>({1, 2, 3});
    auto b = vector_to_list<uint64_t>({10, 20, 30});
    auto result = better_zip<uint64_t, uint64_t>(a, b);
    auto vec = list_to_pairs<uint64_t, uint64_t>(result);
    ASSERT(vec.size() == 3);
    ASSERT(vec[0].first == 1 && vec[0].second == 10);
    ASSERT(vec[1].first == 2 && vec[1].second == 20);
    ASSERT(vec[2].first == 3 && vec[2].second == 30);
    std::cout << "Test 3 (zip equal length): PASSED" << std::endl;
  }

  // Test 4: Zip with first list shorter
  {
    auto a = vector_to_list<uint64_t>({1, 2});
    auto b = vector_to_list<uint64_t>({10, 20, 30, 40});
    auto result = better_zip<uint64_t, uint64_t>(a, b);
    auto vec = list_to_pairs<uint64_t, uint64_t>(result);
    ASSERT(vec.size() == 2);
    ASSERT(vec[0].first == 1 && vec[0].second == 10);
    ASSERT(vec[1].first == 2 && vec[1].second == 20);
    std::cout << "Test 4 (first list shorter): PASSED" << std::endl;
  }

  // Test 5: Zip with second list shorter
  {
    auto a = vector_to_list<uint64_t>({1, 2, 3, 4});
    auto b = vector_to_list<uint64_t>({10, 20});
    auto result = better_zip<uint64_t, uint64_t>(a, b);
    auto vec = list_to_pairs<uint64_t, uint64_t>(result);
    ASSERT(vec.size() == 2);
    ASSERT(vec[0].first == 1 && vec[0].second == 10);
    ASSERT(vec[1].first == 2 && vec[1].second == 20);
    std::cout << "Test 5 (second list shorter): PASSED" << std::endl;
  }

  // Test 6: Zip with different types
  {
    auto a = vector_to_list<uint64_t>({1, 2, 3});
    auto b = vector_to_list<bool>({true, false, true});
    auto result = better_zip<uint64_t, bool>(a, b);
    auto vec = list_to_pairs<uint64_t, bool>(result);
    ASSERT(vec.size() == 3);
    ASSERT(vec[0].first == 1 && vec[0].second == true);
    ASSERT(vec[1].first == 2 && vec[1].second == false);
    ASSERT(vec[2].first == 3 && vec[2].second == true);
    std::cout << "Test 6 (different types): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll zip tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
