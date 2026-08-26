#include "lifted_lambda_nested.h"

uint64_t LiftedLambdaNested::depth(const LiftedLambdaNested::t &x) {
  if (std::holds_alternative<typename LiftedLambdaNested::t::L>(x.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0] = std::get<typename LiftedLambdaNested::t::N>(x.v());
    return (depth(*a0) + 1);
  }
}
