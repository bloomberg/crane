#include <reuse_alias.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
ReuseAlias::tree_sum(const std::shared_ptr<ReuseAlias::tree> &t) {
  if (std::holds_alternative<typename ReuseAlias::tree::Leaf>(t->v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename ReuseAlias::tree::Node>(t->v());
    return ((tree_sum(d_a0) + d_a1) + tree_sum(d_a2));
  }
}

std::shared_ptr<ReuseAlias::tree>
ReuseAlias::transform_tree(const std::shared_ptr<ReuseAlias::tree> &t) {
  if (std::holds_alternative<typename ReuseAlias::tree::Leaf>(t->v())) {
    return tree::leaf();
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename ReuseAlias::tree::Node>(t->v());
    return tree::node(d_a0, tree_sum(t), d_a2);
  }
}

std::shared_ptr<ReuseAlias::tree>
ReuseAlias::nested_match_reuse(const std::shared_ptr<ReuseAlias::tree> &t,
                               const unsigned int flag) {
  if (std::holds_alternative<typename ReuseAlias::tree::Leaf>(t->v())) {
    return tree::leaf();
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename ReuseAlias::tree::Node>(t->v());
    if (flag <= 0) {
      return tree::node(tree::leaf(), tree_sum(t), d_a2);
    } else {
      unsigned int _x0 = flag - 1;
      return tree::node(d_a0, tree_sum(t), tree::leaf());
    }
  }
}

std::shared_ptr<ReuseAlias::tree>
ReuseAlias::annotate_sum(const std::shared_ptr<ReuseAlias::tree> &t) {
  if (std::holds_alternative<typename ReuseAlias::tree::Leaf>(t->v())) {
    return tree::leaf();
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename ReuseAlias::tree::Node>(t->v());
    return tree::node(annotate_sum(d_a0), tree_sum(t), annotate_sum(d_a2));
  }
}
