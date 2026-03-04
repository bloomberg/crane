#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <match_forward_order_safe.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

MatchForwardOrderSafe::token MatchForwardOrderSafe::choose(const bool b) {
  if (b) {
    return token::A;
  } else {
    return token::B;
  }
}

unsigned int
MatchForwardOrderSafe::encode(const MatchForwardOrderSafe::token x) {
  return [&](void) {
    switch (x) {
    case token::A: {
      return (0 + 1);
    }
    case token::B: {
      return 0;
    }
    }
  }();
}
