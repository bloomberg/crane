// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <stream_match_sv_redefinition.h>

#include <cstdint>
#include <iostream>

#define M StreamMatchSvRedefinition

int main() {
  int fails = 0;
  if (!(M::t == 0)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All stream_match_sv_redefinition tests passed!" << std::endl;
  return fails;
}
