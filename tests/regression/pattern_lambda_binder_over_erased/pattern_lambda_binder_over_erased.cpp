#include "pattern_lambda_binder_over_erased.h"

Nat PatternLambdaBinderOverErased::bump(const Nat &n) { return Nat::s(n); }

Phi<Nat> PatternLambdaBinderOverErased::on_phi(const Phi<Nat> &p) {
  return TFunctor_phi<TFunctor_exp>::template tfmap<Nat, Nat>(bump, p);
}
