#include "fwd_decl_before_concept.h"

std::optional<bool> FwdDeclBeforeConcept::use(const std::optional<Nat> &o) {
  return Functor_Monad<Monad_option>::template fmap<Nat, bool>(
      [](const Nat &n) { return n.eqb(Nat::o()); }, o);
}
