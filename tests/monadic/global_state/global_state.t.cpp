#include "global_state.h"

#include <iostream>
#include <variant>

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
    auto result = GlobalStateTests::new_and_read_both_nat<GlobalStateTests::nat_stref, GlobalStateTests::nat_idx>();
    ASSERT(result.first == 5);
    ASSERT(result.second == 6);
    std::cout << "Test 1 (new_and_read_both_nat): (" << result.first << ", "
              << result.second << ") PASSED" << std::endl;
  }

  // Test 2: fib_Glob 5 returns 5
  {
    auto result =
        GlobalStateTests::fib_Glob<GlobalStateTests::nat_stref, GlobalStateTests::nat_idx>(5);
    ASSERT(result == 5);
    std::cout << "Test 8 (fib_Glob 5): " << result << " PASSED" << std::endl;
  }

  // Test 3: fib_fun 5 returns 5
  {
    auto result = GlobalStateTests::fib_fun(5);
    ASSERT(result == 5);
    std::cout << "Test 9 (fib_fun 5): " << result << " PASSED" << std::endl;
  }

  // Test 4: counter run four times returns 4
  {
    GlobalStateTests::start_counter();
    (void)GlobalStateTests::counter_next(); // first
    (void)GlobalStateTests::counter_next();
    (void)GlobalStateTests::counter_next();
    (void)GlobalStateTests::counter_next();
    auto result = GlobalStateTests::counter_next();
    ASSERT(result == 4);
    std::cout << "Test 4 (counter repeated 4 is 4): " << result << " PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll global state tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
