#include <existential_closure_probe.h>

#include <cassert>
#include <iostream>

int main() {
  using ECP = ExistentialClosureProbe;

  // test1: 10+5=15
  auto r1 = ECP::test1;
  std::cout << "test1 = " << r1 << " (expected 15)" << std::endl;
  assert(r1 == 15u);

  // test2: 42+0=42
  auto r2 = ECP::test2;
  std::cout << "test2 = " << r2 << " (expected 42)" << std::endl;
  assert(r2 == 42u);

  // test3: (5+3)*2=16
  auto r3 = ECP::test3;
  std::cout << "test3 = " << r3 << " (expected 16)" << std::endl;
  assert(r3 == 16u);

  std::cout << "All existential_closure_probe tests passed!" << std::endl;
  return 0;
}
