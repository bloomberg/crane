#include <fold_closure_accum.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Sum all values in a tree.
__attribute__((pure)) unsigned int
FoldClosureAccum::tree_sum(const std::shared_ptr<FoldClosureAccum::tree> &t) {
  return std::visit(
      Overloaded{[](const typename FoldClosureAccum::tree::Leaf _args)
                     -> unsigned int { return 0u; },
                 [](const typename FoldClosureAccum::tree::Node _args)
                     -> unsigned int {
                   return ((tree_sum(_args.d_a0) + _args.d_a1) +
                           tree_sum(_args.d_a2));
                 }},
      t->v());
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
unsigned int FoldClosureAccum::compose_adders(
    const std::shared_ptr<List<std::shared_ptr<FoldClosureAccum::tree>>> &trees,
    const unsigned int _x0) {
  throw std::logic_error("untranslatable curried proof term");
}
