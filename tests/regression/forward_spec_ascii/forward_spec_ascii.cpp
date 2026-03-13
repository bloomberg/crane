#include <forward_spec_ascii.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int
ForwardSpecAscii::helper_nat(const unsigned int n) {
  return (std::move(n) + 1);
}

__attribute__((pure)) unsigned int
ForwardSpecAscii::bump_node(const std::shared_ptr<ForwardSpecAscii::node> &x) {
  return std::visit(
      Overloaded{[](const typename ForwardSpecAscii::node::ANode _args)
                     -> unsigned int {
                   unsigned int n = _args.d_a0;
                   return helper_nat(std::move(n));
                 },
                 [](const typename ForwardSpecAscii::node::BNode _args)
                     -> unsigned int {
                   unsigned int n = _args.d_a0;
                   return helper_nat(std::move(n));
                 }},
      x->v());
}
