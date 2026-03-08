#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <program_cycles.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int
ProgramCycles::cycles(const std::shared_ptr<ProgramCycles::state> &_x,
                      const ProgramCycles::instruction _x0) {
  return 8u;
}

unsigned int ProgramCycles::program_cycles(
    const std::shared_ptr<ProgramCycles::state> &s,
    const std::shared_ptr<List<ProgramCycles::instruction>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<ProgramCycles::instruction>::nil _args)
              -> unsigned int { return 0u; },
          [&](const typename List<ProgramCycles::instruction>::cons _args)
              -> unsigned int {
            ProgramCycles::instruction i = _args._a0;
            std::shared_ptr<List<ProgramCycles::instruction>> rest = _args._a1;
            return (cycles(s, i) + program_cycles(s, std::move(rest)));
          }},
      prog->v());
}
