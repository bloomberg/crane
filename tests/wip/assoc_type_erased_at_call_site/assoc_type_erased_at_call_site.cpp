#include "assoc_type_erased_at_call_site.h"

/// Both parameters have the same Rocq type, written at a named instance.
Nat AssocTypeErasedAtCallSite::tag_of(const std::pair<Nat, List<Nat>> &,
                                      ptr b) {
  return b.first;
}

Nat AssocTypeErasedAtCallSite::go(const Nat &) {
  return tag_of(PointerV<IPZ>::null(), PointerV<IPZ>::null());
}
