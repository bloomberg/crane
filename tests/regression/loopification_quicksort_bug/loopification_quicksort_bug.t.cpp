
#include "loopification_quicksort_bug.h"


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
  // Test 1: quicksort_fun sorts a list
  {
    auto result = QuicksortFun::test_quicksort_fun({});
    // sorted list: [4,51,126,127,2412,5981,74879,212498,2749812]

    ASSERT(result == "[ 4, 51, 126, 127, 2412, 5981, 10645, 74879, 212498, 2749812,  ]");
    std::cout << "Test 1 (quicksort_fun [212498;127;5981;2749812;74879;126;4;51;2412;10645])"
    << " outputs" << result << std::endl;

    if (testStatus == 0) {
        std::cout << "\nAll quicksort tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
  }

}
