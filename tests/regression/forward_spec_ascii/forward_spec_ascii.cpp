#include <forward_spec_ascii.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
ForwardSpecAscii::helper_nat(unsigned int n) {
  return (n + 1);
}

__attribute__((pure)) unsigned int
ForwardSpecAscii::bump_node(const ForwardSpecAscii::node &x) {
  if (std::holds_alternative<typename ForwardSpecAscii::node::ANode>(x.v())) {
    const auto &[d_a0] =
        std::get<typename ForwardSpecAscii::node::ANode>(x.v());
    return helper_nat(d_a0);
  } else {
    const auto &[d_a0] =
        std::get<typename ForwardSpecAscii::node::BNode>(x.v());
    return helper_nat(d_a0);
  }
}
