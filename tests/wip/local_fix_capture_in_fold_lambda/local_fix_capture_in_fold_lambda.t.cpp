// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <local_fix_capture_in_fold_lambda.h>

#include <cstdint>
#include <iostream>

#define M LocalFixCaptureInFoldLambda

int main() {
  int fails = 0;
  auto lf = M::tree::leaf();
  if (!(M::tree_obs(M::g2(lf, std::nullopt, 0)) == 1)) { std::cout << "FAIL: M::tree_obs(M::g2(lf, std::nullopt, 0))" << std::endl; ++fails; }
  if (!(M::tree_obs(M::g3(lf, std::nullopt, 0)) == 1)) { std::cout << "FAIL: M::tree_obs(M::g3(lf, std::nullopt, 0))" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All local_fix_capture_in_fold_lambda tests passed!" << std::endl;
  return fails;
}
