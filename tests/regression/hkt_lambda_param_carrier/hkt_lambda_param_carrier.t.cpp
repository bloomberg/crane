#include <hkt_lambda_param_carrier.h>
#include <cassert>

int main() {
  auto r = HktLambdaParamCarrier::run(std::optional<Nat>(Nat::o()));
  assert(r.has_value());
  return 0;
}
