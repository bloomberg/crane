#include "fold_closure_accum.h"

/// Sum all values in a tree.
uint64_t FoldClosureAccum::tree_sum(const FoldClosureAccum::tree &t) {
  if (std::holds_alternative<typename FoldClosureAccum::tree::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename FoldClosureAccum::tree::Node>(t.v());
    return ((tree_sum(*a0) + a1) + tree_sum(*a2));
  }
}

/// Build a composed function by folding over a list of trees.
/// Each step takes the accumulated function and the current tree,
/// producing a new function that adds tree_sum of the current tree
/// to the accumulated function's result.
///
/// BUG HYPOTHESIS: Each fold step creates a closure &acc, &t that
/// captures the previous closure (acc) and the current tree (t).
/// If captures are by reference, the previous closure is stack-local
/// and dies when the fold step returns, creating a dangling chain.
uint64_t
FoldClosureAccum::compose_adders(const List<FoldClosureAccum::tree> &trees,
                                 uint64_t _x0) {
  return trees.template fold_right<std::function<uint64_t(uint64_t)>>(
      [](FoldClosureAccum::tree t, std::function<uint64_t(uint64_t)> acc)
          -> std::function<uint64_t(uint64_t)> {
        return [=](uint64_t x) mutable { return (acc(x) + tree_sum(t)); };
      },
      [](uint64_t x) { return x; })(_x0);
}
