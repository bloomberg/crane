#include <algorithm>
#include <any>
#include <cassert>
#include <decode_opcode_4_wf_edge_0047.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> DecodeOpcode4WfEdge0047::rom(
    const std::shared_ptr<DecodeOpcode4WfEdge0047::state> &s) {
  return s->rom;
}
