#include "monad_alias_of_applied.h"

MonadAliasOfApplied::EOUP<Nat> MonadAliasOfApplied::extract(bool b,
                                                            const Nat &n) {
  if (b) {
    return Monad0::template ret<MonadAliasOfApplied::EOUP_Monad, Nat>(
        Nat::s(n));
  } else {
    return Monad0::template ret<MonadAliasOfApplied::EOU_monad,
                                MonadAliasOfApplied::MaybePoison<Nat>>(
        MaybePoison<Nat>::pois());
  }
}
