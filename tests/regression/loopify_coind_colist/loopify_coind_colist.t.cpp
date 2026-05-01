#include "loopify_coind_colist.h"

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
std::vector<T> list_to_vec(const List<T> &l) {
  std::vector<T> result;
  const List<T> *cur = &l;
  while (std::holds_alternative<typename List<T>::Cons>(cur->v())) {
    auto &c = std::get<typename List<T>::Cons>(cur->v());
    result.push_back(c.d_a0);
    cur = c.d_a1.get();
  }
  return result;
}

int main() {
  // Test 1: comap (*2) [1,2,3] = [2,4,6]
  {
    auto v = list_to_vec(LoopifyCoindColist::test_comap);
    ASSERT(v.size() == 3);
    ASSERT(v[0] == 2);
    ASSERT(v[1] == 4);
    ASSERT(v[2] == 6);
    std::cout << "Test 1 (comap): PASSED" << std::endl;
  }

  // Test 2: cotake 2 [10,20,30] = [10,20]
  {
    auto v = list_to_vec(LoopifyCoindColist::test_cotake);
    ASSERT(v.size() == 2);
    ASSERT(v[0] == 10);
    ASSERT(v[1] == 20);
    std::cout << "Test 2 (cotake): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll loopify_coind_colist tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
