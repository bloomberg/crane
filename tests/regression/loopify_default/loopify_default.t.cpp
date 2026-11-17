#include <loopify_default.h>

#include <cassert>

int main() {
  assert(LoopifyDefault::merged_len == 6);
  assert(LoopifyDefault::merged_sum == 21);
  assert(LoopifyDefault::merged_head == 1);
  return 0;
}
