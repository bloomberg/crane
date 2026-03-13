#include <mutual_indexed.h>

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
MutualIndexed::even_val(const unsigned int _x,
                        const std::shared_ptr<MutualIndexed::EvenTree> &t) {
  return std::visit(
      Overloaded{[](const typename MutualIndexed::EvenTree::ELeaf _args)
                     -> unsigned int { return 0u; },
                 [](const typename MutualIndexed::EvenTree::ENode _args)
                     -> unsigned int {
                   unsigned int v = _args.d_a1;
                   return std::move(v);
                 }},
      t->v());
}

__attribute__((pure)) unsigned int
MutualIndexed::odd_val(const unsigned int _x,
                       const std::shared_ptr<MutualIndexed::OddTree> &t) {
  return std::visit(
      Overloaded{[](const typename MutualIndexed::OddTree::ONode _args)
                     -> unsigned int {
        unsigned int v = _args.d_a1;
        return std::move(v);
      }},
      t->v());
}
