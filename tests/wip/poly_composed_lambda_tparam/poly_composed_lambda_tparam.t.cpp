// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <poly_composed_lambda_tparam.h>

#include <cstdint>
#include <iostream>

#define M PolyComposedLambdaTparam

int main() {
  int fails = 0;
  if (!(M::t == 1)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All poly_composed_lambda_tparam tests passed!" << std::endl;
  return fails;
}
