#include "loopify_itree_reified.h"

#include <iostream>

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

int main() {
  // Test 1: count_taus on a Ret tree = 0 (no Tau nodes)
  {
    ASSERT(LoopifyItreeReified::test_count == 0);
    std::cout << "Test 1 (count_taus on Ret): PASSED" << std::endl;
  }

  // Test 2: count_taus can also be called directly
  {
    auto t = ITree<unsigned int>::ret(42u);
    ASSERT(LoopifyItreeReified::count_taus(10, t) == 0);
    std::cout << "Test 2 (count_taus direct call): PASSED" << std::endl;
  }

  // Test 3: pass cofixpoint on Ret 42 preserves structure (0 Taus)
  {
    auto ret_tree = ITree<unsigned int>::ret(42u);
    auto passed = LoopifyItreeReified::pass<unsigned int>(ret_tree);
    ASSERT(LoopifyItreeReified::count_taus(10, passed) == 0);
    std::cout << "Test 3 (pass on Ret): PASSED" << std::endl;
  }

  // Test 4: pass cofixpoint on Tau(Ret 42) preserves the Tau (1 Tau)
  {
    auto tau_tree =
        ITree<unsigned int>::tau(ITree<unsigned int>::ret(42u));
    auto passed = LoopifyItreeReified::pass<unsigned int>(tau_tree);
    ASSERT(LoopifyItreeReified::count_taus(10, passed) == 1);
    std::cout << "Test 4 (pass on Tau): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll loopify_itree_reified tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
