#include "hk_carrier_written_at_partial_app.h"

Nat HkCarrierWrittenAtPartialApp::bump(const Nat &n) { return Nat::s(n); }

Phi<Nat> HkCarrierWrittenAtPartialApp::on_phi(const Phi<Nat> &p) {
  return TFunctor_phi<TFunctor_exp>::template tfmap<Nat, Nat>(bump, p);
}
