#include <forward_spec_ascii.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
ForwardSpecAscii::helper_nat(const unsigned int n) {
  return (n + 1);
}

__attribute__((pure)) unsigned int
ForwardSpecAscii::bump_node(const std::shared_ptr<ForwardSpecAscii::node> &x) {
  if (std::holds_alternative<typename ForwardSpecAscii::node::ANode>(x->v())) {
    const auto &_m =
        *std::get_if<typename ForwardSpecAscii::node::ANode>(&x->v());
    return helper_nat(_m.d_a0);
  } else {
    const auto &_m =
        *std::get_if<typename ForwardSpecAscii::node::BNode>(&x->v());
    return helper_nat(_m.d_a0);
  }
}
