#include "loopify_coind_stream.h"

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

template <typename T>
std::vector<T> list_to_vec(std::shared_ptr<List<T>> l) {
  std::vector<T> result;
  while (std::holds_alternative<typename List<T>::Cons>(l->v())) {
    auto &c = std::get<typename List<T>::Cons>(l->v());
    result.push_back(c.d_a0);
    l = c.d_a1;
  }
  return result;
}

int main() {
  // Test 1: take 5 nats = [0, 1, 2, 3, 4]
  {
    auto v = list_to_vec(LoopifyCoindStream::test_nats_5);
    ASSERT(v.size() == 5);
    ASSERT(v[0] == 0);
    ASSERT(v[1] == 1);
    ASSERT(v[2] == 2);
    ASSERT(v[3] == 3);
    ASSERT(v[4] == 4);
    std::cout << "Test 1 (nats): PASSED" << std::endl;
  }

  // Test 2: take 5 doubled = [0, 2, 4, 6, 8]
  {
    auto v = list_to_vec(LoopifyCoindStream::test_doubled_5);
    ASSERT(v.size() == 5);
    ASSERT(v[0] == 0);
    ASSERT(v[1] == 2);
    ASSERT(v[2] == 4);
    ASSERT(v[3] == 6);
    ASSERT(v[4] == 8);
    std::cout << "Test 2 (doubled): PASSED" << std::endl;
  }

  // Test 3: take 5 sum_stream = [0, 3, 6, 9, 12]
  {
    auto v = list_to_vec(LoopifyCoindStream::test_sum_5);
    ASSERT(v.size() == 5);
    ASSERT(v[0] == 0);
    ASSERT(v[1] == 3);
    ASSERT(v[2] == 6);
    ASSERT(v[3] == 9);
    ASSERT(v[4] == 12);
    std::cout << "Test 3 (sum_stream): PASSED" << std::endl;
  }

  // Test 4: take 8 fibs = [0, 1, 1, 2, 3, 5, 8, 13]
  {
    auto v = list_to_vec(LoopifyCoindStream::test_fibs_8);
    ASSERT(v.size() == 8);
    ASSERT(v[0] == 0);
    ASSERT(v[1] == 1);
    ASSERT(v[2] == 1);
    ASSERT(v[3] == 2);
    ASSERT(v[4] == 3);
    ASSERT(v[5] == 5);
    ASSERT(v[6] == 8);
    ASSERT(v[7] == 13);
    std::cout << "Test 4 (fibs): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll loopify_coind_stream tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
