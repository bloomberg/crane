#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <program_cycles_two_nop.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int
ProgramCyclesTwoNop::acc(const std::shared_ptr<ProgramCyclesTwoNop::state> &s) {
  return s->acc;
}

unsigned int ProgramCyclesTwoNop::cycles(
    const std::shared_ptr<ProgramCyclesTwoNop::state> &_x,
    const ProgramCyclesTwoNop::instruction _x0) {
  return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
}

unsigned int ProgramCyclesTwoNop::program_cycles(
    const std::shared_ptr<ProgramCyclesTwoNop::state> &s,
    const std::shared_ptr<List<ProgramCyclesTwoNop::instruction>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<ProgramCyclesTwoNop::instruction>::nil _args)
              -> unsigned int { return 0; },
          [&](const typename List<ProgramCyclesTwoNop::instruction>::cons _args)
              -> unsigned int {
            ProgramCyclesTwoNop::instruction i = _args._a0;
            std::shared_ptr<List<ProgramCyclesTwoNop::instruction>> rest =
                _args._a1;
            return (cycles(s, i) + program_cycles(s, std::move(rest)));
          }},
      prog->v());
}
