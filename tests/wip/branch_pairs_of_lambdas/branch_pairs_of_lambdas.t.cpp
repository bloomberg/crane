// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <branch_pairs_of_lambdas.h>

#include <cstdint>
#include <iostream>

#define M BranchPairsOfLambdas

int main() {
  int fails = 0;
  if (!(M::f(true) == 0)) { std::cout << "FAIL: M::f(true)" << std::endl; ++fails; }
  if (!(M::f(false) == 1)) { std::cout << "FAIL: M::f(false)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All branch_pairs_of_lambdas tests passed!" << std::endl;
  return fails;
}
