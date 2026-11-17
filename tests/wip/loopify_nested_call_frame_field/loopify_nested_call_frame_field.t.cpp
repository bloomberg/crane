// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <loopify_nested_call_frame_field.h>

#include <cstdint>
#include <iostream>

#define M LoopifyNestedCallFrameField

int main() {
  int fails = 0;
  auto l = List<std::pair<uint64_t, bool>>::cons(std::make_pair(UINT64_C(1), true), List<std::pair<uint64_t, bool>>::nil());
  auto a = List<uint64_t>::cons(5, List<uint64_t>::nil());
  if (!(M::g(l, a).length() == 0)) { std::cout << "FAIL: M::g(l, a).length()" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All loopify_nested_call_frame_field tests passed!" << std::endl;
  return fails;
}
