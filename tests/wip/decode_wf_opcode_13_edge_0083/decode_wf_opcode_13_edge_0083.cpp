#include <algorithm>
#include <any>
#include <cassert>
#include <decode_wf_opcode_13_edge_0083.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<DecodeWfOpcode13Edge0083::Shadow>
DecodeWfOpcode13Edge0083::bump(
    const std::shared_ptr<DecodeWfOpcode13Edge0083::Shadow> &x) {
  return [&](void) {
    unsigned int n = x->Shadow::value;
    return std::make_shared<DecodeWfOpcode13Edge0083::Shadow>(
        Shadow::shadow{(n + 1)});
  }();
}
