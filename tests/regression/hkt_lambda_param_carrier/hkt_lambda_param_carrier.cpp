#include "hkt_lambda_param_carrier.h"

std::optional<Nat> HktLambdaParamCarrier::run(const std::optional<Nat> &o) {
  return twice<HktLambdaParamCarrier::OptM, Nat>(
      o, [](Nat n) { return std::make_optional<Nat>(Nat::s(n)); });
}
