#include "monad_alias_of_applied.h"

MonadAliasOfApplied::EOUP<Nat> MonadAliasOfApplied::extract(bool b,
                                                            const Nat &n) {
  if (b) {
    return MonadAliasOfApplied::EOUP_Monad::template ret<Nat>(Nat::s(n));
  } else {
    return MonadAliasOfApplied::EOU_monad::template ret<
        MonadAliasOfApplied::MaybePoison<Nat>>(MaybePoison<Nat>::pois());
  }
}
