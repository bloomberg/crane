// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <local_fix_capture_in_fold_lambda.h>

#include <cstdint>
#include <iostream>

#define M LocalFixCaptureInFoldLambda

int main() {
  int fails = 0;
  auto lf = M::tree::leaf();
  auto nd = lf.tins(3);
  if (!(lf.g2(std::nullopt, 0).tree_obs() == 1)) { std::cout << "FAIL: lf.g2(std::nullopt, 0).tree_obs()" << std::endl; ++fails; }
  if (!(lf.g3(std::nullopt, 0).tree_obs() == 1)) { std::cout << "FAIL: lf.g3(std::nullopt, 0).tree_obs()" << std::endl; ++fails; }
  if (!(nd.g3(std::nullopt, 0).tree_obs() == 10)) { std::cout << "FAIL: nd.g3(std::nullopt, 0).tree_obs()" << std::endl; ++fails; }
  if (!std::holds_alternative<List<std::optional<uint64_t>>::Nil>(nd.g5().v())) { std::cout << "FAIL: nd.g5() is nil" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All local_fix_capture_in_fold_lambda tests passed!" << std::endl;
  return fails;
}
