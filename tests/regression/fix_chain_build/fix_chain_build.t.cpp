#include <fix_chain_build.h>

#include <cassert>
#include <iostream>

int main() {
  using FCB = FixChainBuild;

  // test1: build_chain(1). base=1, step(2)=3. Total=4.
  // BUG: step captures n and prev by [&] from destroyed stack frame.
  auto r1 = FCB::test1;
  std::cout << "test1 = " << r1 << " (expected 4)" << std::endl;
  assert(r1 == 4u);

  // test2: build_chain(2). base=2, step(0)=2. Total=4.
  auto r2 = FCB::test2;
  std::cout << "test2 = " << r2 << " (expected 4)" << std::endl;
  assert(r2 == 4u);

  // test3: build_chain(3). base=3, step(0)=3. Total=6.
  auto r3 = FCB::test3;
  std::cout << "test3 = " << r3 << " (expected 6)" << std::endl;
  assert(r3 == 6u);

  std::cout << "All fix_chain_build tests passed!" << std::endl;
  return 0;
}
