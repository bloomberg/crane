#include <loopify_constant_local_fix.h>

#include <cassert>
#include <iostream>

int main() {
  auto a = LoopifyConstantLocalFix::from_n(1000000);
  std::cout << "from_n = " << a << std::endl;
  assert(a == 1000000);
  auto b = LoopifyConstantLocalFix::million;
  std::cout << "million = " << b << std::endl;
  assert(b == 1000000);
  return 0;
}
