#include <fix_via_simple_lambda.h>

#include <cassert>
#include <iostream>

int main() {
  using FVSL = FixViaSimpleLambda;

  // test1: base=42, double_add(5) = 42+10 = 52,
  //        triple_add(5) = 42+15 = 57, total = 109.
  // BUG: fixpoints captured by [=] in outer lambda, but internal
  // [&] closures still reference dangling stack variable 'base'.
  auto r1 = FVSL::test1;
  std::cout << "test1 = " << r1 << " (expected 109)" << std::endl;
  assert(r1 == 109u);

  // test2: base=200, double_add(0)+triple_add(0) = 200+200 = 400.
  auto r2 = FVSL::test2;
  std::cout << "test2 = " << r2 << " (expected 400)" << std::endl;
  assert(r2 == 400u);

  // test3: base=10, double_add(20)=50, triple_add(20)=70, total=120.
  auto r3 = FVSL::test3;
  std::cout << "test3 = " << r3 << " (expected 120)" << std::endl;
  assert(r3 == 120u);

  std::cout << "All fix_via_simple_lambda tests passed!" << std::endl;
  return 0;
}
