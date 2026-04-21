#include <reuse_lambda_capture.h>

#include <cassert>
#include <iostream>

int main() {
  using RLC = ReuseLambdaCapture;

  auto r1 = RLC::test1;
  std::cout << "test1 = " << r1 << " (expected 3)" << std::endl;
  assert(r1 == 3u);

  auto r2 = RLC::test2;
  std::cout << "test2 = " << r2 << " (expected 6)" << std::endl;
  assert(r2 == 6u);

  std::cout << "All tests passed!" << std::endl;
  return 0;
}
