#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <reset_state.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<ResetState::state_full>
ResetState::reset_state_full(std::shared_ptr<ResetState::state_full> s) {
  return std::make_shared<ResetState::state_full>(
      state_full{0u, s->regs_full, false, 0u, List<unsigned int>::ctor::nil_(),
                 s->ram_sys, s->rom});
}

std::shared_ptr<ResetState::state_minimal>
ResetState::reset_state_minimal(std::shared_ptr<ResetState::state_minimal> s) {
  return std::make_shared<ResetState::state_minimal>(state_minimal{
      s->regs_minimal, false, 0u, s->ram_sys_minimal, s->rom_minimal});
}
