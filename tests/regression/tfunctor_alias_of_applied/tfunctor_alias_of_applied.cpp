#include "tfunctor_alias_of_applied.h"

TfunctorAliasOfApplied::mcfg<Nat> TfunctorAliasOfApplied::convert(
    const TfunctorAliasOfApplied::modul<Nat, TfunctorAliasOfApplied::cfg<Nat>>
        &m) {
  return TfunctorAliasOfApplied::ConvertTyp_mcfg::convert_typ(Nat::s(Nat::o()),
                                                              m);
}
