#include <this_capture_record.h>

#include <cassert>
#include <iostream>

int main() {
  using TCR = ThisCaptureRecord;

  // test1: cr_add(10)=15, cr_mul(3)=15. Total=30.
  auto r1 = TCR::test1;
  std::cout << "test1 = " << r1 << " (expected 30)" << std::endl;
  assert(r1 == 30u);

  // test2: cr_add(0)=60, cr_mul(1)=60. Total=120.
  auto r2 = TCR::test2;
  std::cout << "test2 = " << r2 << " (expected 120)" << std::endl;
  assert(r2 == 120u);

  // test3: flag=1, tree_sum=100. cr_mul always returns tree_sum=100.
  auto r3 = TCR::test3;
  std::cout << "test3 = " << r3 << " (expected 100)" << std::endl;
  assert(r3 == 100u);

  std::cout << "All this_capture_record tests passed!" << std::endl;
  return 0;
}
