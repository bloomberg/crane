#include "method_type_names_module_alias.h"

MethodTypeNamesModuleAlias::Bag::flag
MethodTypeNamesModuleAlias::Bag::get(const MethodTypeNamesModuleAlias::Bag &b) {
  return b.a.eqb(Nat::o());
}

MethodTypeNamesModuleAlias::Tree::size MethodTypeNamesModuleAlias::Tree::count(
    const MethodTypeNamesModuleAlias::Tree::tree &t) {
  if (std::holds_alternative<
          typename MethodTypeNamesModuleAlias::Tree::tree::Leaf>(t.v())) {
    return Nat::s(Nat::o());
  } else {
    const auto &[l0, r0] =
        std::get<typename MethodTypeNamesModuleAlias::Tree::tree::Node>(t.v());
    return count(*l0).add(count(*r0));
  }
}
