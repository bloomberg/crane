#include "hk_call_carrier_erased.h"

List<crane::obj> TFunctor_list(const crane::fn<crane::obj(crane::obj)> &x0_,
                               const List<crane::obj> &x1_) {
  return x1_.template map<crane::obj>(x0_);
}

box<crane::obj> TFunctor_box(const crane::fn<crane::obj(crane::obj)> &f,
                             const box<crane::obj> &b) {
  return box<crane::obj>{f(b.b_payload)};
}

Nat HkCallCarrierErased::bump(const Nat &n) { return Nat::s(n); }

List<box<Nat>> HkCallCarrierErased::on_boxes(const List<box<Nat>> &l) {
  return tfmap<List<box<crane::obj>>, Nat, Nat>(
      []() {
        return [](crane::fn<crane::obj(crane::obj)> _x0,
                  const auto &_x1) -> List<box<crane::obj>> {
          return TFunctor_list_<box<crane::obj>>(
              [](auto &&_ec0, box<crane::obj> _ec1) {
                return TFunctor_box(_ec0, _ec1);
              },
              _x0, crane_convert<List<box<crane::obj>>>(_x1));
        };
      }(),
      bump, l);
}

outer<Nat, List<Nat>>
HkCallCarrierErased::on_outer(const outer<Nat, List<Nat>> &m) {
  return tfmap<outer<crane::obj, List<crane::obj>>, Nat, Nat>(
      []() {
        return [](crane::fn<crane::obj(crane::obj)> _x0,
                  const auto &_x1) -> outer<crane::obj, List<crane::obj>> {
          return TFunctor_outer<List<crane::obj>>(
              [](auto &&_ec0, List<crane::obj> _ec1) {
                return TFunctor_list(_ec0, _ec1);
              },
              _x0, crane_convert<outer<crane::obj, List<crane::obj>>>(_x1));
        };
      }(),
      bump, m);
}
