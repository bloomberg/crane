#include "hk_instance_body_targ_undeclared.h"

Nat HkInstanceBodyTargUndeclared::bump(const Nat &n) { return Nat::s(n); }

std::optional<List<Nat>>
HkInstanceBodyTargUndeclared::on_option(const std::optional<List<Nat>> &o) {
  return TFunctor_option<TFunctor_list>::template tfmap<Nat, Nat>(bump, o);
}

List<List<Nat>>
HkInstanceBodyTargUndeclared::on_list(const List<List<Nat>> &l) {
  return TFunctor_list_<TFunctor_list>::template tfmap<Nat, Nat>(bump, l);
}
