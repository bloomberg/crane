// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <reuse_nonatomic_const_v_mut.h>

#include <cstdint>
#include <iostream>

#define M ReuseNonatomicConstVMut

int main() {
  int fails = 0;
  if (!(M::t == 1)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All reuse_nonatomic_const_v_mut tests passed!" << std::endl;
  return fails;
}
