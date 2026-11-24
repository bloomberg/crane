#include <loopify_param_moved_read.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = LoopifyParamMovedRead::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 0);
  return 0;
}
