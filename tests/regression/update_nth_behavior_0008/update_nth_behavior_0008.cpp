#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <update_nth_behavior_0008.h>
#include <variant>

unsigned int UpdateNthBehavior0008::cycles(
    const std::shared_ptr<UpdateNthBehavior0008::state> &_x,
    const UpdateNthBehavior0008::instruction _x0) {
  return 8u;
}

unsigned int UpdateNthBehavior0008::program_cycles(
    const std::shared_ptr<UpdateNthBehavior0008::state> &s,
    const std::shared_ptr<List<UpdateNthBehavior0008::instruction>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<UpdateNthBehavior0008::instruction>::nil _args)
              -> unsigned int { return 0u; },
          [&](const typename List<UpdateNthBehavior0008::instruction>::cons
                  _args) -> unsigned int {
            UpdateNthBehavior0008::instruction i = _args._a0;
            std::shared_ptr<List<UpdateNthBehavior0008::instruction>> rest =
                _args._a1;
            return (cycles(s, i) + program_cycles(s, std::move(rest)));
          }},
      prog->v());
}
