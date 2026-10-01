#include "fmap_erased_lambda_param.h"

std::optional<Sum<Exc, Dv>> FmapErasedLambdaParam::go(const Nat &n) {
  return raise_right<Monad_option>(std::make_optional<Dv>(Dv::DV_(n)));
}
