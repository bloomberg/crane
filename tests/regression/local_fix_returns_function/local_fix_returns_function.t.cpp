// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <local_fix_returns_function.h>

#include <cstdint>
#include <iostream>

#define M LocalFixReturnsFunction

int main() {
  int fails = 0;
  auto l = List<uint64_t>::cons(1, List<uint64_t>::cons(2, List<uint64_t>::nil()));
  if (!(M::t(l) == 2)) { std::cout << "FAIL: M::t(l)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All local_fix_returns_function tests passed!" << std::endl;
  return fails;
}
