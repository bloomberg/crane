// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "stmonad.h"

#include <iostream>
#include <variant>

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

int main() {
  // Test 1: newAndReadBoth returns (5, 6)
  {
    auto result =
        STMonadTests::new_and_read_both_nat<STMonadTests::nat_idx,
                                            STMonadTests::nat_stref>();
    ASSERT(result.first == 5);
    ASSERT(result.second == 6);
    std::cout << "Test 1 (new_and_read_both_nat): (" << result.first << ", "
              << result.second << ") PASSED" << std::endl;
  }

  // Test 2: tree_simp returns 5
  {
    auto result = STMonadTests::tree_simp_nat<STMonadTests::nat_idx,
                                              STMonadTests::nat_stref>();
    ASSERT(result == 5);
    std::cout << "Test 2 (tree_simp_nat): " << result << " PASSED" << std::endl;
  }

  // Test 3: tree_simp_another returns 6
  {
    auto result = STMonadTests::tree_simp_another_nat<STMonadTests::nat_stref,
                                                      STMonadTests::nat_idx>();
    ASSERT(result == 6);
    std::cout << "Test 3 (tree_simp_another_nat): " << result << " PASSED"
              << std::endl;
  }

  // Test 4: newAndReadBoth returns (false, true)
  {
    auto result =
        STMonadTests::new_and_read_both_bool<STMonadTests::nat_idx,
                                             STMonadTests::nat_stref>();
    ASSERT(result.first == false);
    ASSERT(result.second == true);
    std::cout << "Test 4 (new_and_read_both_bool): (" << result.first << ", "
              << result.second << ") PASSED" << std::endl;
  }

  // Test 5: tree_simp_bool returns true
  {
    auto result = STMonadTests::tree_simp_bool<STMonadTests::nat_idx,
                                               STMonadTests::nat_stref>();
    ASSERT(result == true);
    std::cout << "Test 5 (tree_simp_bool): " << result << " PASSED"
              << std::endl;
  }

  // Test 6: array_simp_fixed_init returns 5
  {
    auto result = STMonadTests::array_simp_fixed_init();
    ASSERT(result == 5);
    std::cout << "Test 6 (array_simp_fixed_init): " << result << " PASSED"
              << std::endl;
  }

  // Test 7: array_simp_list returns 5,4
  {
    auto result = STMonadTests::array_simp_list();
    ASSERT(result.first.first == 5);
    ASSERT(result.first.second == 4);
    ASSERT(result.second.hd(0) == 5);
    ASSERT(result.second.tl().hd(0) == 4);
    ASSERT(result.second.tl().tl().hd(0) == 3);
    ASSERT(result.second.tl().tl().tl().hd(0) == 2);
    std::cout << "Test 7 (array_simp_list): " << result.first.first << ","
              << result.first.second << ", [" << result.second.hd(0) << ","
              << result.second.tl().hd(0) << ","
              << result.second.tl().tl().hd(0) << ","
              << result.second.tl().tl().tl().hd(0) << "]"
              << " PASSED" << std::endl;
  }

  // Test 8: fib_ST 5 returns 5
  {
    auto result =
        STMonadTests::fib_ST<STMonadTests::nat_stref, STMonadTests::nat_idx>(5);
    ASSERT(result == 5);
    std::cout << "Test 8 (fibSt 5): " << result << " PASSED" << std::endl;
  }

  // Test 9: fib_fun 5 returns 5
  {
    auto result = STMonadTests::fib_fun(5);
    ASSERT(result == 5);
    std::cout << "Test 9 (fib_fun 5): " << result << " PASSED" << std::endl;
  }

  // Test 10: quicksort_fun sorts a list
  {
    List<uint64_t> lst = List<uint64_t>::cons(
        4, List<uint64_t>::cons(
               1, List<uint64_t>::cons(2, List<uint64_t>::nil())));
    auto result = STMonadTests::quicksort_fun(lst);
    ASSERT(result.hd(6) == 1);
    ASSERT(result.tl().hd(6) == 2);
    ASSERT(result.tl().tl().hd(6) == 4);
    std::cout << "Test 10 (quicksort_fun [4;2;1])"
              << " outputs [" << result.hd(6) << ", " << result.tl().hd(6)
              << ", " << result.tl().tl().hd(6) << "], len: " << result.length()
              << " PASSED" << std::endl;
  }

  {
    List<uint64_t> lst = List<uint64_t>::cons(
        4, List<uint64_t>::cons(
               1, List<uint64_t>::cons(2, List<uint64_t>::nil())));
    auto result = STMonadTests::quicksort_ST(lst);
    ASSERT(result.hd(6) == 1);
    ASSERT(result.tl().hd(6) == 2);
    ASSERT(result.tl().tl().hd(6) == 4);
    std::cout << "Test 11 (quicksort [4;2;1])"
              << " outputs [" << result.hd(6) << ", " << result.tl().hd(6)
              << ", " << result.tl().tl().hd(6) << "], len: " << result.length()
              << " PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll stmonad tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
