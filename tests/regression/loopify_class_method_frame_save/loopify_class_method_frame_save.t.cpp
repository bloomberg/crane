// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <loopify_class_method_frame_save.h>

#include <cstdint>
#include <iostream>

#define M LoopifyClassMethodFrameSave

int main() {
  int fails = 0;
  auto l = List<uint64_t>::cons(1, List<uint64_t>::cons(2, List<uint64_t>::nil()));
  if (!(M::g(l) == true)) { std::cout << "FAIL: M::g(l)" << std::endl; ++fails; }
  if (!(M::h(3) == 6)) { std::cout << "FAIL: M::h(3)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All loopify_class_method_frame_save tests passed!" << std::endl;
  return fails;
}
