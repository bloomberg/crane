#include <loopify_local_fix_inner_callback.h>

#include <cassert>
#include <cstdio>
#include <utility>

int main() {
  assert(LoopifyLocalFixInnerCallback::small == 9);
  assert(LoopifyLocalFixInnerCallback::ack(std::make_pair(3, 3)) == 61);
  std::printf("loopify_local_fix_inner_callback: ok\n");
  return 0;
}
