#include "sigt_leaf_list_dispatch.h"

/// Attempt to reproduce the residual Newick.h/PPM.h bug: a LIST is built by
/// generically dispatching to another production's result (mirroring how
/// the real grammar builds e.g. TREES ::= TREE TREES via a generic
/// `find_predicate_and_action`-style call whose return type is
/// production-dependent, hence erased to std::any), and consing that
/// generic result onto an accumulating list, then forwarding the whole list
/// to a concretely-typed top-level function. Earlier attempts using a
/// directly concretely-typed list nat (not built via generic dispatch)
/// did NOT reproduce the bug -- this tries forcing genuine erasure of the
/// list itself via a single generic run function whose return type
/// domty (projT1 e) depends on the runtime witness e, just like
/// Newick's grammar-entry dispatch.
bool wrap_list(const List<uint64_t> &xs) { return xs.length() == xs.length(); }

domty run(const SigT<uint64_t, std::function<std::any(std::monostate)>> &e) {
  return e.projT2()(std::monostate{});
}

bool check(std::monostate) { return wrap_list(run(entry_trees)); }
