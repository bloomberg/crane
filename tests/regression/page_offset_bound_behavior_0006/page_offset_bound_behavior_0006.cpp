#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <page_offset_bound_behavior_0006.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int PageOffsetBoundBehavior0006::acc(
    const std::shared_ptr<PageOffsetBoundBehavior0006::state> &s) {
  return s->acc;
}

unsigned int PageOffsetBoundBehavior0006::cycles(
    const std::shared_ptr<PageOffsetBoundBehavior0006::state> &_x,
    const PageOffsetBoundBehavior0006::instruction _x0) {
  return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
}

unsigned int PageOffsetBoundBehavior0006::program_cycles(
    const std::shared_ptr<PageOffsetBoundBehavior0006::state> &s,
    const std::shared_ptr<List<PageOffsetBoundBehavior0006::instruction>>
        &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<PageOffsetBoundBehavior0006::instruction>::nil
                 _args) -> unsigned int { return 0; },
          [&](const typename List<PageOffsetBoundBehavior0006::instruction>::
                  cons _args) -> unsigned int {
            PageOffsetBoundBehavior0006::instruction i = _args._a0;
            std::shared_ptr<List<PageOffsetBoundBehavior0006::instruction>>
                rest = _args._a1;
            return (cycles(s, i) + program_cycles(s, std::move(rest)));
          }},
      prog->v());
}
