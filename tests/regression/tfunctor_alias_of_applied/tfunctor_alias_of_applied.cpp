#include "tfunctor_alias_of_applied.h"

List<crane::obj>
TfunctorAliasOfApplied::TFunctor_list(crane::fn<crane::obj(crane::obj)> x0_,
                                      const List<crane::obj> &x1_) {
  return x1_.template map<crane::obj>(std::move(x0_));
}

TfunctorAliasOfApplied::cfg<crane::obj> TfunctorAliasOfApplied::TFunctor_cfg(
    crane::fn<crane::obj(crane::obj)> f,
    const TfunctorAliasOfApplied::cfg<crane::obj> &c) {
  return cfg<crane::obj>{f(c.blk)};
}

TfunctorAliasOfApplied::mcfg<Nat> TfunctorAliasOfApplied::convert(
    const TfunctorAliasOfApplied::modul<Nat, TfunctorAliasOfApplied::cfg<Nat>>
        &m) {
  return convert_typ<TfunctorAliasOfApplied::mcfg>(ConvertTyp_mcfg,
                                                   Nat::s(Nat::o()), m);
}
