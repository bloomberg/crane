#include <algorithm>
#include <any>
#include <cassert>
#include <decode_wf_opcode_7_edge_0077.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> DecodeWfOpcode7Edge0077::regs(
    const std::shared_ptr<DecodeWfOpcode7Edge0077::state> &s) {
  return s->regs;
}

std::shared_ptr<List<unsigned int>> DecodeWfOpcode7Edge0077::rom(
    const std::shared_ptr<DecodeWfOpcode7Edge0077::state> &s) {
  return s->rom;
}
