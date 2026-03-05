#include <algorithm>
#include <any>
#include <cassert>
#include <decode_encode_id_behavior_0028.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> DecodeEncodeIdBehavior0028::regs(
    const std::shared_ptr<DecodeEncodeIdBehavior0028::state> &s) {
  return s->regs;
}

bool DecodeEncodeIdBehavior0028::carry(
    const std::shared_ptr<DecodeEncodeIdBehavior0028::state> &s) {
  return s->carry;
}

unsigned int DecodeEncodeIdBehavior0028::pc(
    const std::shared_ptr<DecodeEncodeIdBehavior0028::state> &s) {
  return s->pc;
}

std::shared_ptr<List<unsigned int>> DecodeEncodeIdBehavior0028::ram_sys(
    const std::shared_ptr<DecodeEncodeIdBehavior0028::state> &s) {
  return s->ram_sys;
}

std::shared_ptr<List<unsigned int>> DecodeEncodeIdBehavior0028::rom(
    const std::shared_ptr<DecodeEncodeIdBehavior0028::state> &s) {
  return s->rom;
}

std::shared_ptr<DecodeEncodeIdBehavior0028::state>
DecodeEncodeIdBehavior0028::reset_state(
    std::shared_ptr<DecodeEncodeIdBehavior0028::state> s) {
  return std::make_shared<DecodeEncodeIdBehavior0028::state>(
      state{s->regs, false, 0, s->ram_sys, s->rom});
}
