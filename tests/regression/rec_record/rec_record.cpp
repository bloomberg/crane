#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <rec_record.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int
RecRecord::rlist_sum(const std::shared_ptr<RecRecord::rlist<unsigned int>> &l) {
  return std::visit(
      Overloaded{[](const typename RecRecord::rlist<unsigned int>::rnil _args)
                     -> unsigned int { return 0; },
                 [](const typename RecRecord::rlist<unsigned int>::rcons _args)
                     -> unsigned int {
                   unsigned int x = _args._a0;
                   std::shared_ptr<RecRecord::rlist<unsigned int>> rest =
                       _args._a1;
                   return (std::move(x) + rlist_sum(std::move(rest)));
                 }},
      l->v());
}

unsigned int
RecRecord::rnode_depth(const std::shared_ptr<RecRecord::RNode> &r) {
  if (r->rn_next.has_value()) {
    std::shared_ptr<RecRecord::RNode> next = *r->rn_next;
    return (rnode_depth(next) + 1);
  } else {
    return (0 + 1);
  }
}
