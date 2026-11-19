// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <stream_match_v_mut_missing.h>

#include <cstdint>
#include <iostream>

#define M StreamMatchVMutMissing

int main() {
  int fails = 0;
  if (!(M::g(3).first == 0)) { std::cout << "FAIL: M::g(3).first" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All stream_match_v_mut_missing tests passed!" << std::endl;
  return fails;
}
