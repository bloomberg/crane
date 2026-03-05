#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <ram_write_then_read_main_behavior_0042.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int RamWriteThenReadMainBehavior0042::acc(
    const std::shared_ptr<RamWriteThenReadMainBehavior0042::state> &s) {
  return s->acc;
}

unsigned int RamWriteThenReadMainBehavior0042::cycles(
    const std::shared_ptr<RamWriteThenReadMainBehavior0042::state> &_x,
    const RamWriteThenReadMainBehavior0042::instruction _x0) {
  return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
}

unsigned int RamWriteThenReadMainBehavior0042::program_cycles(
    const std::shared_ptr<RamWriteThenReadMainBehavior0042::state> &s,
    const std::shared_ptr<List<RamWriteThenReadMainBehavior0042::instruction>>
        &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<
              RamWriteThenReadMainBehavior0042::instruction>::nil _args)
              -> unsigned int { return 0; },
          [&](const typename List<
              RamWriteThenReadMainBehavior0042::instruction>::cons _args)
              -> unsigned int {
            RamWriteThenReadMainBehavior0042::instruction i = _args._a0;
            std::shared_ptr<List<RamWriteThenReadMainBehavior0042::instruction>>
                rest = _args._a1;
            return (cycles(s, i) + program_cycles(s, std::move(rest)));
          }},
      prog->v());
}
