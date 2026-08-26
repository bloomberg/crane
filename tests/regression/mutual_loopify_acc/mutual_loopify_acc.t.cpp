#include <mutual_loopify_acc.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = MutualLoopifyAcc::go(10);
  std::cout << "go 10 = " << r << " (want 10)" << std::endl;
  assert(r == 10);
  return 0;
}
