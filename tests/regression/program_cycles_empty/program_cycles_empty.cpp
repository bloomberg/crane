#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <program_cycles_empty.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int
ProgramCyclesEmpty::acc(const std::shared_ptr<ProgramCyclesEmpty::state> &s) {
  return s->acc;
}

unsigned int
ProgramCyclesEmpty::cycles(const std::shared_ptr<ProgramCyclesEmpty::state> &_x,
                           const ProgramCyclesEmpty::instruction _x0) {
  return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
}

unsigned int ProgramCyclesEmpty::program_cycles(
    const std::shared_ptr<ProgramCyclesEmpty::state> &s,
    const std::shared_ptr<List<ProgramCyclesEmpty::instruction>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<ProgramCyclesEmpty::instruction>::nil _args)
              -> unsigned int { return 0; },
          [&](const typename List<ProgramCyclesEmpty::instruction>::cons _args)
              -> unsigned int {
            ProgramCyclesEmpty::instruction i = _args._a0;
            std::shared_ptr<List<ProgramCyclesEmpty::instruction>> rest =
                _args._a1;
            return (cycles(s, i) + program_cycles(s, std::move(rest)));
          }},
      prog->v());
}
