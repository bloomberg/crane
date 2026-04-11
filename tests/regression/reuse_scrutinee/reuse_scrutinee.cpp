#include <reuse_scrutinee.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Extract the value from the left subtree.
/// This accesses the Node's d_a0 field (left subtree).
__attribute__((pure)) unsigned int
ReuseScrutinee::left_val(const std::shared_ptr<ReuseScrutinee::tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename ReuseScrutinee::tree::Leaf) -> unsigned int {
            return 0u;
          },
          [](const typename ReuseScrutinee::tree::Node _args) -> unsigned int {
            return std::visit(
                Overloaded{[](const typename ReuseScrutinee::tree::Leaf)
                               -> unsigned int { return 0u; },
                           [](const typename ReuseScrutinee::tree::Node _args0)
                               -> unsigned int { return _args0.d_a1; }},
                _args.d_a0->v());
          }},
      t->v());
}

/// Extract the value from the right subtree.
__attribute__((pure)) unsigned int
ReuseScrutinee::right_val(const std::shared_ptr<ReuseScrutinee::tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename ReuseScrutinee::tree::Leaf) -> unsigned int {
            return 0u;
          },
          [](const typename ReuseScrutinee::tree::Node _args) -> unsigned int {
            return std::visit(
                Overloaded{[](const typename ReuseScrutinee::tree::Leaf)
                               -> unsigned int { return 0u; },
                           [](const typename ReuseScrutinee::tree::Node _args0)
                               -> unsigned int { return _args0.d_a1; }},
                _args.d_a2->v());
          }},
      t->v());
}

/// Sum of left and right subtree values.
__attribute__((pure)) unsigned int
ReuseScrutinee::subtree_sum(const std::shared_ptr<ReuseScrutinee::tree> &t) {
  return (left_val(t) + right_val(t));
}
