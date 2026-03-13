#include <rec_record.h>

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
RecRecord::rlist_sum(const std::shared_ptr<RecRecord::rlist<unsigned int>> &l) {
  return std::visit(
      Overloaded{[](const typename RecRecord::rlist<unsigned int>::Rnil _args)
                     -> unsigned int { return 0u; },
                 [](const typename RecRecord::rlist<unsigned int>::Rcons _args)
                     -> unsigned int {
                   unsigned int x = _args.d_a0;
                   std::shared_ptr<RecRecord::rlist<unsigned int>> rest =
                       _args.d_a1;
                   return (std::move(x) + rlist_sum(std::move(rest)));
                 }},
      l->v());
}

__attribute__((pure)) unsigned int
RecRecord::rnode_depth(const std::shared_ptr<RecRecord::RNode> &r) {
  if (r->rn_next.has_value()) {
    std::shared_ptr<RecRecord::RNode> next = *r->rn_next;
    return (rnode_depth(next) + 1);
  } else {
    return 1u;
  }
}
