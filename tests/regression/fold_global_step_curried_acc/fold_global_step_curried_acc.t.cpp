// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <fold_global_step_curried_acc.h>

#include <cstdint>
#include <iostream>

#define M FoldGlobalStepCurriedAcc

int main() {
  int fails = 0;
  auto e = List<uint64_t>::nil();
  auto one = List<uint64_t>::cons(1, e);
  auto zero_one = List<uint64_t>::cons(0, one);
  if (!(M::t1(e) == 7)) { std::cout << "FAIL: M::t1(e)" << std::endl; ++fails; }
  if (!(M::t1(one) == 7)) { std::cout << "FAIL: M::t1(one)" << std::endl; ++fails; }
  if (!(M::t1(zero_one) == 0)) { std::cout << "FAIL: M::t1(zero_one)" << std::endl; ++fails; }
  if (!(M::t2(zero_one) == 2)) { std::cout << "FAIL: M::t2(zero_one)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All fold_global_step_curried_acc tests passed!" << std::endl;
  return fails;
}
