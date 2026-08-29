#include "lifted_lambda_forward_ref.h"

uint64_t LiftedLambdaForwardRef::later(const LiftedLambdaForwardRef::t &x) {
  if (std::holds_alternative<typename LiftedLambdaForwardRef::t::L>(x.v())) {
    return UINT64_C(1);
  } else {
    return UINT64_C(2);
  }
}
