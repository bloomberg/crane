#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <match_forward_order.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

Node::shadow MatchForwardOrder::pick(const bool b) {
  if (b) {
    return Node::shadow::TagA;
  } else {
    return Node::shadow::TagB;
  }
}
