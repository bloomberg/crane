#include "lifted_lambda_two_users.h"

uint64_t LiftedLambdaTwoUsers::depth(const LiftedLambdaTwoUsers::t &x) {
  if (std::holds_alternative<typename LiftedLambdaTwoUsers::t::L>(x.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0] = std::get<typename LiftedLambdaTwoUsers::t::N>(x.v());
    return (depth(*a0) + 1);
  }
}
