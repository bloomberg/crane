#include <fold_closure_build.h>

#include <cassert>
#include <iostream>

int main() {
  using FCB = FoldClosureBuild;

  // test1: compose_adders [10,20,30] 7 = 67 (safe, uses [=])
  auto r1 = FCB::test1;
  std::cout << "test1 = " << r1 << " (expected 67)" << std::endl;
  assert(r1 == 67u);

  // test2: f(0) + f(100) where f = compose_adders [5,10]
  // f(0) = 15, f(100) = 115, total = 130 (safe, uses [=])
  auto r2 = FCB::test2;
  std::cout << "test2 = " << r2 << " (expected 130)" << std::endl;
  assert(r2 == 130u);

  // test3: apply_all (collect_adders [10,20,30]) 5
  // = (30+5) + (20+5) + (10+5) = 75 (safe, uses [=])
  auto r3 = FCB::test3;
  std::cout << "test3 = " << r3 << " (expected 75)" << std::endl;
  assert(r3 == 75u);

  // test4: compose_with_fix [10] 5 = 15
  // BUG: fixpoint go captures acc and h by [&] inside fold callback.
  // When fold callback returns, acc and h are destroyed but go still references them.
  auto r4 = FCB::test4;
  std::cout << "test4 = " << r4 << " (expected 15)" << std::endl;
  assert(r4 == 15u);

  // test5: compose_with_fix [10,20] 7 = 37
  // BUG: same as test4 but with two fold iterations, creating a chain of
  // dangling fixpoints where each depends on the previous.
  auto r5 = FCB::test5;
  std::cout << "test5 = " << r5 << " (expected 37)" << std::endl;
  assert(r5 == 37u);

  std::cout << "All fold_closure_build tests passed!" << std::endl;
  return 0;
}
