#include "sigt_leaf_list_dispatch.h"

bool wrap_list(const List<uint64_t> &xs) { return xs.length() == xs.length(); }

domty run(const SigT<uint64_t, std::function<std::any(std::monostate)>> &e) {
  return e.projT2()(std::monostate{});
}

bool check(std::monostate) {
  return wrap_list(
      List<uint64_t>(std::any_cast<List<std::any>>(run(entry_trees))));
}
