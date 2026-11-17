#include "hk_call_carrier_erased.h"

Nat HkCallCarrierErased::bump(const Nat &n) { return Nat::s(n); }

List<box<Nat>> HkCallCarrierErased::on_boxes(const List<box<Nat>> &l) {
  return TFunctor_list_<TFunctor_box>::template tfmap<Nat, Nat>(bump, l);
}

outer<Nat, List<Nat>>
HkCallCarrierErased::on_outer(const outer<Nat, List<Nat>> &m) {
  return TFunctor_outer<TFunctor_list>::template tfmap<Nat, Nat>(bump, m);
}
