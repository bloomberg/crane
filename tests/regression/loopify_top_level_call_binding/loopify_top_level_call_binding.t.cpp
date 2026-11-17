#include <loopify_top_level_call_binding.h>

#include <cassert>
#include <cstdio>

int main() {
  using M = LoopifyTopLevelCallBinding;
  assert(M::csum(M::wide) == 10);
  // 100001 cells of 1: deeper than the native recursion survives.
  assert(M::csum(M::chain(100000, 1)) == 100001);
  std::printf("loopify_top_level_call_binding: ok\n");
  return 0;
}
