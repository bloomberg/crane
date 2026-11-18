// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <cofix_thunk_dangling_capture.h>

#include <cstdint>
#include <iostream>

#define M CofixThunkDanglingCapture

int main() {
  int fails = 0;
  if (!(M::t == 0)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All cofix_thunk_dangling_capture tests passed!" << std::endl;
  return fails;
}
