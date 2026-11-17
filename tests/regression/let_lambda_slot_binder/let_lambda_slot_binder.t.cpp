// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <let_lambda_slot_binder.h>

#include <cstdint>
#include <iostream>

#define M LetLambdaSlotBinder

int main() {
  int fails = 0;
  if (!(M::t == 2)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All let_lambda_slot_binder tests passed!" << std::endl;
  return fails;
}
