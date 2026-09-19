#include "monad_method_targ_misnumbered.h"

std::optional<Nat> MonadMethodTargMisnumbered::use(const List<Nat> &l) {
  return monad_fold_right<Monad_option, Nat, Nat>(
      [](const Nat &b, const Nat &a) {
        return std::make_optional<Nat>(b.add(a));
      },
      l, Nat::o());
}
