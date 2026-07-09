#include "type_args_extraction.h"
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

  {
    auto result = double_n(2);
    ASSERT(result == 4);
    std::cout << "Test 1 (double_n 2 is 4): " << result
              << " PASSED" << std::endl;
  }

}
