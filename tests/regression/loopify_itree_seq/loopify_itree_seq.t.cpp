#include "loopify_itree_seq.h"

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
  // Test 1: count_down 5 = 5
  {
    ASSERT(LoopifyItreeSeq::test_count_5() == 5);
    std::cout << "Test 1 (count_down 5): PASSED" << std::endl;
  }

  // Test 2: sum_to 10 = 55
  {
    ASSERT(LoopifyItreeSeq::test_sum_10() == 55);
    std::cout << "Test 2 (sum_to 10): PASSED" << std::endl;
  }

  // Test 3: countdown_list 4 = [4, 3, 2, 1, 0]
  {
    auto clist = LoopifyItreeSeq::test_clist_4();
    auto v = list_to_vec(clist);
    ASSERT(v[0] == 4);
    ASSERT(v[1] == 3);
    ASSERT(v[2] == 2);
    ASSERT(v[3] == 1);
    ASSERT(v[4] == 0);
    std::cout << "Test 3 (countdown_list 4): PASSED" << std::endl;
  }

  // Test 4: delay_ret 5 42 = 42 (cofixpoint, Tau erased, tail recursion)
  {
    ASSERT(LoopifyItreeSeq::test_delay() == 42);
    std::cout << "Test 4 (delay_ret 5 42): PASSED" << std::endl;
  }

  // Test 5: spin and forever are infinite loops (itree _ unit).
  // Verify they compile and are callable (but don't call them — they never
  // return).  A game loop or server would use this pattern.
  {
    (void)&LoopifyItreeSeq::spin;
    (void)&LoopifyItreeSeq::forever;
    std::cout << "Test 5 (spin/forever compile): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll loopify_itree_seq tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
