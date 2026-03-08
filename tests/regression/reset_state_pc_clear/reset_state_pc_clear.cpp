#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <reset_state_pc_clear.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<ResetStatePcClear::state>
ResetStatePcClear::reset_state(std::shared_ptr<ResetStatePcClear::state> s) {
  return std::make_shared<ResetStatePcClear::state>(
      state{s->regs, false, 0u, s->ram_sys, s->rom});
}
