#include <loopify_shadow_update_reads_binding.h>

#include <cassert>
#include <cstdio>

int main() {
  // ((2 + 1) * 10) + 3.
  assert(LoopifyShadowUpdateReadsBinding::result == 33);
  std::printf("loopify_shadow_update_reads_binding: ok\n");
  return 0;
}
