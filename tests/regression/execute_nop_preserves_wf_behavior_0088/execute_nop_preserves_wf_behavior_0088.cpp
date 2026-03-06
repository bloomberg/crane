#include <algorithm>
#include <any>
#include <cassert>
#include <execute_nop_preserves_wf_behavior_0088.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> ExecuteNopPreservesWfBehavior0088::rom(
    const std::shared_ptr<ExecuteNopPreservesWfBehavior0088::state> &s) {
  return s->rom;
}

unsigned int ExecuteNopPreservesWfBehavior0088::fetch_byte(
    const std::shared_ptr<ExecuteNopPreservesWfBehavior0088::state> &s,
    const unsigned int addr) {
  return s->rom->nth(addr, 0);
}
