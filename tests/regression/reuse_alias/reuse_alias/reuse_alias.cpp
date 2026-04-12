#include <reuse_alias.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
ReuseAlias::tree_sum(const std::shared_ptr<ReuseAlias::tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename ReuseAlias::tree::Leaf) -> unsigned int {
            return 0u;
          },
          [](const typename ReuseAlias::tree::Node _args) -> unsigned int {
            return ((tree_sum(_args.d_a0) + _args.d_a1) + tree_sum(_args.d_a2));
          }},
      t->v());
}

/// BUG PATTERN 1: Reuse optimization with function call on scrutinee.
/// match t with Node l v r => Node l (some_fn t) r
/// If reuse fires: moves l and r out of t, then calls some_fn(t).
/// But t's fields are now null/moved, so some_fn reads garbage.
///
/// Different from reuse_scrutinee: here the function is applied
/// directly to the scrutinee, not to a separate variable.
std::shared_ptr<ReuseAlias::tree>
ReuseAlias::transform_tree(std::shared_ptr<ReuseAlias::tree> t) {
  if (t.use_count() == 1 && t->v().index() == 0) {
    auto &_rf = std::get<0>(t->v_mut());
    return t;
  } else {
    return std::visit(
        Overloaded{
            [](const typename ReuseAlias::tree::Leaf)
                -> std::shared_ptr<ReuseAlias::tree> { return tree::leaf(); },
            [&](const typename ReuseAlias::tree::Node _args)
                -> std::shared_ptr<ReuseAlias::tree> {
              return tree::node(_args.d_a0, tree_sum(t), _args.d_a2);
            }},
        t->v());
  }
}

/// BUG PATTERN 2: Nested match where inner match uses outer scrutinee.
/// Outer match on t, inner match on something else, but result
/// uses both outer pattern vars AND the outer scrutinee.
std::shared_ptr<ReuseAlias::tree>
ReuseAlias::nested_match_reuse(std::shared_ptr<ReuseAlias::tree> t,
                               const unsigned int flag) {
  if (t.use_count() == 1 && t->v().index() == 0) {
    auto &_rf = std::get<0>(t->v_mut());
    return t;
  } else {
    return std::visit(
        Overloaded{
            [](const typename ReuseAlias::tree::Leaf)
                -> std::shared_ptr<ReuseAlias::tree> { return tree::leaf(); },
            [&](const typename ReuseAlias::tree::Node _args)
                -> std::shared_ptr<ReuseAlias::tree> {
              if (flag <= 0) {
                return tree::node(tree::leaf(), tree_sum(t), _args.d_a2);
              } else {
                unsigned int _x0 = flag - 1;
                return tree::node(_args.d_a0, tree_sum(t), tree::leaf());
              }
            }},
        t->v());
  }
}

/// BUG PATTERN 3: Recursive function where the recursive call uses
/// the original tree while pattern vars are also used in constructor.
/// map_tree modifies each node's value but the modification depends
/// on the FULL subtree structure.
std::shared_ptr<ReuseAlias::tree>
ReuseAlias::annotate_sum(std::shared_ptr<ReuseAlias::tree> t) {
  if (t.use_count() == 1 && t->v().index() == 0) {
    auto &_rf = std::get<0>(t->v_mut());
    return t;
  } else {
    return std::visit(
        Overloaded{
            [](const typename ReuseAlias::tree::Leaf)
                -> std::shared_ptr<ReuseAlias::tree> { return tree::leaf(); },
            [&](const typename ReuseAlias::tree::Node _args)
                -> std::shared_ptr<ReuseAlias::tree> {
              return tree::node(annotate_sum(_args.d_a0), tree_sum(t),
                                annotate_sum(_args.d_a2));
            }},
        t->v());
  }
}
