#include <loopify_frame_ptr_escape.h>

#include <cassert>
#include <iostream>

int main() {
  // Rocq: Compute (go 4) = 15.
  auto r = LoopifyFramePtrEscape::go(4u);
  std::cout << "walk = " << r << std::endl;
  assert(r == 15u);
  return 0;
}
