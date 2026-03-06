#include <algorithm>
#include <any>
#include <cassert>
#include <decode_edge_0019.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<DecodeEdge0019::Shadow>
DecodeEdge0019::bump(const std::shared_ptr<DecodeEdge0019::Shadow> &x) {
  return [&](void) {
    unsigned int n = x->Shadow::value;
    return std::make_shared<DecodeEdge0019::Shadow>(Shadow::shadow{(n + 1)});
  }();
}
