#include "sigt_leaf_list_dispatch.h"

/// A LIST is built by generically dispatching to another production's
/// result (mirroring how a grammar builds e.g. TREES ::= TREE TREES via a
/// generic `find_predicate_and_action`-style call whose return type is
/// production-dependent, hence erased to std::any), and consing that
/// generic result onto an accumulating list, then forwarding the whole list
/// to a concretely-typed top-level function. run's return type
/// domty (projT1 e) depends on the runtime witness e, so its call sites
/// only see std::any; the erased list is boxed as List<std::any>, while
/// wrap_list expects the concrete List<uint64_t>.
bool wrap_list(const List<uint64_t> &xs) { return xs.length() == xs.length(); }

domty run(const SigT<uint64_t, std::function<std::any(std::monostate)>> &e) {
  return e.projT2()(std::monostate{});
}

bool check(std::monostate) {
  return wrap_list(
      List<uint64_t>(std::any_cast<List<std::any>>(run(entry_trees))));
}
