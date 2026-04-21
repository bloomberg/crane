#include <fix_direct_return.h>

#include <cassert>
#include <iostream>

int main() {
  using FDR = FixDirectReturn;

  // test1: make_callback(42)(id) = id(42) + 43 = 85.
  // BUG: inner fixpoint add uses [&] capturing base.
  // Even though outer lambda uses [=], the copied std::function
  // add still has dangling [&] references.
  auto r1 = FDR::test1;
  std::cout << "test1 = " << r1 << " (expected 85)" << std::endl;
  assert(r1 == 85u);

  // test2: make_callback(10)(x => x*2) = 20 + 11 = 31.
  auto r2 = FDR::test2;
  std::cout << "test2 = " << r2 << " (expected 31)" << std::endl;
  assert(r2 == 31u);

  // test3: nested callbacks = cb1(5)(_ => cb2(100)(id)) = _ + 6 where _ = 100 + 101 = 201. Total = 201 + 6 = 207.
  auto r3 = FDR::test3;
  std::cout << "test3 = " << r3 << " (expected 207)" << std::endl;
  assert(r3 == 207u);

  std::cout << "All fix_direct_return tests passed!" << std::endl;
  return 0;
}
