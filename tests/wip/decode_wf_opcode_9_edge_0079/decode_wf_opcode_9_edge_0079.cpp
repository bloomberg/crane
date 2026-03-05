#include <algorithm>
#include <any>
#include <cassert>
#include <decode_wf_opcode_9_edge_0079.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> DecodeWfOpcode9Edge0079::rom(
    const std::shared_ptr<DecodeWfOpcode9Edge0079::state> &s) {
  return s->rom;
}
