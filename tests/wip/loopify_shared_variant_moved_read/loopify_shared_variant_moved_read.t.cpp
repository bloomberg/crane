#include <loopify_shared_variant_moved_read.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = LoopifySharedVariantMovedRead::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 1);
  return 0;
}
