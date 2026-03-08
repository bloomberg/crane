#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <reset_state_memory_preserve.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<ResetStateMemoryPreserve::state>
ResetStateMemoryPreserve::reset_state(
    std::shared_ptr<ResetStateMemoryPreserve::state> s) {
  return std::make_shared<ResetStateMemoryPreserve::state>(
      state{0u, s->regs, false, 0u, List<unsigned int>::ctor::nil_(),
            s->ram_sys, s->rom});
}
