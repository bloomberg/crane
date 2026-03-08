#include <algorithm>
#include <any>
#include <cassert>
#include <cycles_jms_constant.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int CyclesJmsConstant::cycles(
    const std::shared_ptr<CyclesJmsConstant::state> &_x,
    const std::shared_ptr<CyclesJmsConstant::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename CyclesJmsConstant::instruction::JMS _args)
                     -> unsigned int { return 24u; },
                 [](const typename CyclesJmsConstant::instruction::NOP _args)
                     -> unsigned int { return 8u; }},
      i->v());
}
