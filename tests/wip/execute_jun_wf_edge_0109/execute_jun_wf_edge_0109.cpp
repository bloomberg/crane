#include <algorithm>
#include <any>
#include <cassert>
#include <execute_jun_wf_edge_0109.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> ExecuteJunWfEdge0109::regs(
    const std::shared_ptr<ExecuteJunWfEdge0109::state> &s) {
  return s->regs;
}

std::shared_ptr<List<unsigned int>> ExecuteJunWfEdge0109::rom(
    const std::shared_ptr<ExecuteJunWfEdge0109::state> &s) {
  return s->rom;
}
