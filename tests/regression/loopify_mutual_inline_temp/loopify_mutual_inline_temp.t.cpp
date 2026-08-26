#include <loopify_mutual_inline_temp.h>

#include <cassert>
#include <iostream>

int main() {
  // Rocq: Compute (go 8) = 16, Compute (go 7) = 12.
  auto r8 = LoopifyMutualInlineTemp::go(8u);
  auto r7 = LoopifyMutualInlineTemp::go(7u);
  std::cout << "go 8 = " << r8 << " (want 16)" << std::endl;
  std::cout << "go 7 = " << r7 << " (want 12)" << std::endl;
  assert(r8 == 16u);
  assert(r7 == 12u);
  return 0;
}
