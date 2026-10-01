#include "hk_instance_body_targ_undeclared.h"

List<crane::obj> TFunctor_list(crane::fn<crane::obj(crane::obj)> x0_,
                               const List<crane::obj> &x1_) {
  return x1_.template map<crane::obj>(std::move(x0_));
}

Nat HkInstanceBodyTargUndeclared::bump(const Nat &n) { return Nat::s(n); }

std::optional<List<Nat>>
HkInstanceBodyTargUndeclared::on_option(const std::optional<List<Nat>> &o) {
  return tfmap<std::optional<List<crane::obj>>, Nat, Nat>(
      []() {
        return [](crane::fn<crane::obj(crane::obj)> _x0,
                  const auto &_x1) -> std::optional<List<crane::obj>> {
          return TFunctor_option<List<crane::obj>>(
              [](auto &&_ec0, List<crane::obj> _ec1) {
                return TFunctor_list(_ec0, _ec1);
              },
              _x0, crane_convert<std::optional<List<crane::obj>>>(_x1));
        };
      }(),
      bump, o);
}

List<List<Nat>>
HkInstanceBodyTargUndeclared::on_list(const List<List<Nat>> &l) {
  return tfmap<List<List<crane::obj>>, Nat, Nat>(
      []() {
        return [](crane::fn<crane::obj(crane::obj)> _x0,
                  const auto &_x1) -> List<List<crane::obj>> {
          return TFunctor_list_<List<crane::obj>>(
              [](auto &&_ec0, List<crane::obj> _ec1) {
                return TFunctor_list(_ec0, _ec1);
              },
              _x0, crane_convert<List<List<crane::obj>>>(_x1));
        };
      }(),
      bump, l);
}
