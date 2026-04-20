#include <simple_lambda_field_capture.h>

#include <cassert>
#include <iostream>

int main() {
  using SLFC = SimpleLambdaFieldCapture;

  // test1: l=[10,20,30], h=10, t=[20,30], mylist_sum(t)=50.
  //        f(5) = 5 + 10 + 50 = 65.
  // CONTROL: simple lambda uses [=] capture, should be safe.
  auto r1 = SLFC::test1;
  std::cout << "test1 = " << r1 << " (expected 65)" << std::endl;
  assert(r1 == 65u);

  // test2: l=[100,200], h=100, mylist_sum(t)=200, f(0)=300.
  auto r2 = SLFC::test2;
  std::cout << "test2 = " << r2 << " (expected 300)" << std::endl;
  assert(r2 == 300u);

  std::cout << "All simple_lambda_field_capture tests passed!" << std::endl;
  return 0;
}
