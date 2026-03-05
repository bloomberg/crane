#include <algorithm>
#include <any>
#include <cassert>
#include <decode_opcode_2_wf_edge_0045.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> DecodeOpcode2WfEdge0045::regs(
    const std::shared_ptr<DecodeOpcode2WfEdge0045::state> &s) {
  return s->regs;
}

std::shared_ptr<List<unsigned int>> DecodeOpcode2WfEdge0045::rom(
    const std::shared_ptr<DecodeOpcode2WfEdge0045::state> &s) {
  return s->rom;
}
