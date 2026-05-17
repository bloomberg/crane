#include "fold_closure_accum.h"

/// Sum all values in a tree.
unsigned int FoldClosureAccum::tree_sum(const FoldClosureAccum::tree &t) {
  if (std::holds_alternative<typename FoldClosureAccum::tree::Leaf>(t.v())) {
    return 0u;
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
unsigned int
FoldClosureAccum::compose_adders(const List<FoldClosureAccum::tree> &trees,
                                 unsigned int _x0) {
  return trees.template fold_right<std::function<unsigned int(unsigned int)>>(
      [](FoldClosureAccum::tree t,
         std::function<unsigned int(unsigned int)> acc)
          -> std::function<unsigned int(unsigned int)> {
        return [=](unsigned int x) mutable { return (acc(x) + tree_sum(t)); };
      },
      [](unsigned int x) { return x; })(_x0);
}
