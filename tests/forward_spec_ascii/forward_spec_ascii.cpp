#include "forward_spec_ascii.h"

uint64_t ForwardSpecAscii::helper_nat(uint64_t n) { return (n + 1); }

uint64_t ForwardSpecAscii::bump_node(const ForwardSpecAscii::node &x) {
  if (std::holds_alternative<typename ForwardSpecAscii::node::ANode>(x.v())) {
    const auto &[a0] = std::get<typename ForwardSpecAscii::node::ANode>(x.v());
    return helper_nat(a0);
  } else {
    const auto &[a0] = std::get<typename ForwardSpecAscii::node::BNode>(x.v());
    return helper_nat(a0);
  }
}
