// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "program_fixpoint.h"

#include <iostream>
#include <vector>

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

std::vector<uint64_t>
list_to_vector(const List<uint64_t> &l) {
  std::vector<uint64_t> result;
  const List<uint64_t> *cur = &l;
  while (std::holds_alternative<typename List<uint64_t>::Cons>(cur->v())) {
    auto &c = std::get<typename List<uint64_t>::Cons>(cur->v());
    result.push_back(c.a0);
    cur = c.a1.get();
  }
  return result;
}

List<uint64_t>
vector_to_list(const std::vector<uint64_t> &vec) {
  auto result = List<uint64_t>::nil();
  for (auto it = vec.rbegin(); it != vec.rend(); ++it) {
    result = List<uint64_t>::cons(*it, std::move(result));
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
    auto l2 = List<uint64_t>::nil();
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
