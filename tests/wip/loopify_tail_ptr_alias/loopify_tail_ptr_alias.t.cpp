#include <loopify_tail_ptr_alias.h>

#include <cassert>
#include <iostream>

int main() {
  // Rocq: Compute (go 6) = 21.
  auto r = LoopifyTailPtrAlias::go(6u);
  std::cout << "rot = " << r << std::endl;
  assert(r == 21u);
  return 0;
}
