// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <fold_curried_accumulator.h>

#include <cstdint>
#include <iostream>

#define M FoldCurriedAccumulator

int main() {
  int fails = 0;
  auto l = List<uint64_t>::cons(1, List<uint64_t>::cons(2, List<uint64_t>::nil()));
  if (!(M::g(l, 10, 20) == 12)) { std::cout << "FAIL: M::g(l, 10, 20)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All fold_curried_accumulator tests passed!" << std::endl;
  return fails;
}
