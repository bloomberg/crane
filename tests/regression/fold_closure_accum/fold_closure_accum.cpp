#include <fold_closure_accum.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Sum all values in a tree.
__attribute__((pure)) unsigned int
FoldClosureAccum::tree_sum(const std::shared_ptr<FoldClosureAccum::tree> &t) {
  if (std::holds_alternative<typename FoldClosureAccum::tree::Leaf>(t->v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename FoldClosureAccum::tree::Node>(t->v());
    return ((tree_sum(d_a0) + d_a1) + tree_sum(d_a2));
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
__attribute__((pure)) unsigned int FoldClosureAccum::compose_adders(
    const std::shared_ptr<List<std::shared_ptr<FoldClosureAccum::tree>>> &trees,
    const unsigned int _x0) {
  return trees->template fold_right<std::function<unsigned int(unsigned int)>>(
      [](std::shared_ptr<FoldClosureAccum::tree> t,
         const std::function<unsigned int(unsigned int)> acc)
          -> std::function<unsigned int(unsigned int)> {
        return [=](const unsigned int x) mutable {
          return (acc(x) + tree_sum(t));
        };
      },
      [](const unsigned int x) { return x; })(_x0);
}
