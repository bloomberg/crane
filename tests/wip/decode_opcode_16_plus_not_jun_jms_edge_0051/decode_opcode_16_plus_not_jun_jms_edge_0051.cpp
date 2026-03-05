#include <algorithm>
#include <any>
#include <cassert>
#include <decode_opcode_16_plus_not_jun_jms_edge_0051.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<DecodeOpcode16PlusNotJunJmsEdge0051::Shadow>
DecodeOpcode16PlusNotJunJmsEdge0051::bump(
    const std::shared_ptr<DecodeOpcode16PlusNotJunJmsEdge0051::Shadow> &x) {
  return [&](void) {
    unsigned int n = x->Shadow::value;
    return std::make_shared<DecodeOpcode16PlusNotJunJmsEdge0051::Shadow>(
        Shadow::shadow{(n + 1)});
  }();
}
