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
  return std::visit(
      Overloaded{[](const typename ForwardSpecAscii::node::ANode _args)
                     -> unsigned int { return helper_nat(_args.d_a0); },
                 [](const typename ForwardSpecAscii::node::BNode _args)
                     -> unsigned int { return helper_nat(_args.d_a0); }},
      x->v());
}
