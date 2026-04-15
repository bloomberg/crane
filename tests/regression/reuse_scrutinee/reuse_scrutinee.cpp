#include <reuse_scrutinee.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Extract the value from the left subtree.
/// This accesses the Node's d_a0 field (left subtree).
__attribute__((pure)) unsigned int
ReuseScrutinee::left_val(const std::shared_ptr<ReuseScrutinee::tree> &t) {
  if (std::holds_alternative<typename ReuseScrutinee::tree::Leaf>(t->v())) {
    return 0u;
  } else {
    const auto &_m = *std::get_if<typename ReuseScrutinee::tree::Node>(&t->v());
    auto &&_sv0 = _m.d_a0;
    if (std::holds_alternative<typename ReuseScrutinee::tree::Leaf>(
            _sv0->v())) {
      return 0u;
    } else {
      const auto &_m0 =
          *std::get_if<typename ReuseScrutinee::tree::Node>(&_sv0->v());
      return _m0.d_a1;
    }
  }
}

/// Extract the value from the right subtree.
__attribute__((pure)) unsigned int
ReuseScrutinee::right_val(const std::shared_ptr<ReuseScrutinee::tree> &t) {
  if (std::holds_alternative<typename ReuseScrutinee::tree::Leaf>(t->v())) {
    return 0u;
  } else {
    const auto &_m = *std::get_if<typename ReuseScrutinee::tree::Node>(&t->v());
    auto &&_sv0 = _m.d_a2;
    if (std::holds_alternative<typename ReuseScrutinee::tree::Leaf>(
            _sv0->v())) {
      return 0u;
    } else {
      const auto &_m0 =
          *std::get_if<typename ReuseScrutinee::tree::Node>(&_sv0->v());
      return _m0.d_a1;
    }
  }
}

/// Sum of left and right subtree values.
__attribute__((pure)) unsigned int
ReuseScrutinee::subtree_sum(const std::shared_ptr<ReuseScrutinee::tree> &t) {
  return (left_val(t) + right_val(t));
}
