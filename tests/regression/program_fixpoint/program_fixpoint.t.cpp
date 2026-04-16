// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "program_fixpoint.h"

#include <iostream>
#include <memory>
#include <variant>
#include <vector>

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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

std::shared_ptr<List<unsigned int>>
vector_to_list(const std::vector<unsigned int> &vec) {
  auto result = List<unsigned int>::nil();
  for (auto it = vec.rbegin(); it != vec.rend(); ++it) {
    result = List<unsigned int>::cons(*it, result);
  }
  return result;
}

int main() {
  // Test 1: interleave two lists
  {
    auto l1 = vector_to_list({1, 3, 5});
    auto l2 = vector_to_list({2, 4, 6});
    auto result = ProgFix::interleave(l1, l2);
    auto vec = list_to_vector(result);
    ASSERT(vec.size() == 6);
    ASSERT(vec[0] == 1);
    ASSERT(vec[1] == 2);
    ASSERT(vec[2] == 3);
    ASSERT(vec[3] == 4);
    ASSERT(vec[4] == 5);
    ASSERT(vec[5] == 6);
    std::cout << "Test 1 (interleave): PASSED" << std::endl;
  }

  // Test 2: interleave with empty
  {
    auto l1 = vector_to_list({1, 2, 3});
    auto l2 = List<unsigned int>::nil();
    auto result = ProgFix::interleave(l1, l2);
    auto vec = list_to_vector(result);
    ASSERT(vec.size() == 3);
    ASSERT(vec[0] == 1);
    ASSERT(vec[1] == 2);
    ASSERT(vec[2] == 3);
    std::cout << "Test 2 (interleave with empty): PASSED" << std::endl;
  }

  // Test 3: test_interleave constant
  {
    auto vec = list_to_vector(ProgFix::test_interleave);
    ASSERT(vec.size() == 6);
    ASSERT(vec[0] == 1);
    ASSERT(vec[1] == 2);
    ASSERT(vec[2] == 3);
    ASSERT(vec[3] == 4);
    ASSERT(vec[4] == 5);
    ASSERT(vec[5] == 6);
    std::cout << "Test 3 (test_interleave): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll Program Fixpoint tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
