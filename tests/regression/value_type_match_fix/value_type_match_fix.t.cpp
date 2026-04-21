#include <value_type_match_fix.h>

#include <cassert>
#include <iostream>

int main() {
  using VTMF = ValueTypeMatchFix;

  // test1: MkTriple(10,20,30), base=60, go(5)=65.
  // BUG: fixpoint captures base (derived from value-type fields) by [&].
  auto r1 = VTMF::test1;
  std::cout << "test1 = " << r1 << " (expected 65)" << std::endl;
  assert(r1 == 65u);

  // test2: MkTriple(100,200,300), base=600, go(0)=600 + noise(55) = 655.
  auto r2 = VTMF::test2;
  std::cout << "test2 = " << r2 << " (expected 655)" << std::endl;
  assert(r2 == 655u);

  // test3: MkTriple(42,0,0), a=42, go(3)=45.
  // Here the fixpoint directly captures the value-type field.
  auto r3 = VTMF::test3;
  std::cout << "test3 = " << r3 << " (expected 45)" << std::endl;
  assert(r3 == 45u);

  std::cout << "All value_type_match_fix tests passed!" << std::endl;
  return 0;
}
