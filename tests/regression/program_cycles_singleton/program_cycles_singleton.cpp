#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <program_cycles_singleton.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int ProgramCyclesSingleton::acc(
    const std::shared_ptr<ProgramCyclesSingleton::state> &s) {
  return s->acc;
}

unsigned int ProgramCyclesSingleton::cycles(
    const std::shared_ptr<ProgramCyclesSingleton::state> &_x,
    const ProgramCyclesSingleton::instruction _x0) {
  return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
}

unsigned int ProgramCyclesSingleton::program_cycles(
    const std::shared_ptr<ProgramCyclesSingleton::state> &s,
    const std::shared_ptr<List<ProgramCyclesSingleton::instruction>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<ProgramCyclesSingleton::instruction>::nil
                 _args) -> unsigned int { return 0; },
          [&](const typename List<ProgramCyclesSingleton::instruction>::cons
                  _args) -> unsigned int {
            ProgramCyclesSingleton::instruction i = _args._a0;
            std::shared_ptr<List<ProgramCyclesSingleton::instruction>> rest =
                _args._a1;
            return (cycles(s, i) + program_cycles(s, std::move(rest)));
          }},
      prog->v());
}
