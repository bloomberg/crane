#include "let_match_type.h"

/// 1. let-bound bool match returning nat
uint64_t LetMatchType::let_match_nat(bool b) {
  uint64_t x;
  if (b) {
    x = UINT64_C(1);
  } else {
    x = UINT64_C(0);
  }
  return (x + x);
}

/// 2. let-bound nat match returning string — TRIGGERS std::any bug
std::string LetMatchType::let_match_string(uint64_t n) {
  std::string s;
  if (n <= 0) {
    s = "zero";
  } else {
    uint64_t _x = n - 1;
    s = "nonzero";
  }
  return s + s;
}

/// 3. let-bound option match
uint64_t LetMatchType::let_match_option(const std::optional<uint64_t> &o) {
  uint64_t x;
  if (o.has_value()) {
    const uint64_t &n = *o;
    x = n;
  } else {
    x = UINT64_C(0);
  }
  return (x + UINT64_C(1));
}

/// 4. let-bound nested bool match
uint64_t LetMatchType::let_nested_bool(bool a, bool b) {
  if (a) {
    if (b) {
      return UINT64_C(3);
    } else {
      return UINT64_C(2);
    }
  } else {
    if (b) {
      return UINT64_C(1);
    } else {
      return UINT64_C(0);
    }
  }
}

/// 5. Multiple let-bound matches
uint64_t LetMatchType::multi_let_match(bool a, bool b) {
  uint64_t x;
  if (a) {
    x = UINT64_C(10);
  } else {
    x = UINT64_C(0);
  }
  uint64_t y;
  if (b) {
    y = UINT64_C(1);
  } else {
    y = UINT64_C(0);
  }
  return (x + y);
}

/// 6. let-bound match used in function argument
uint64_t LetMatchType::let_match_in_arg(uint64_t n) {
  uint64_t x;
  if (n <= 0) {
    x = UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    x = n_;
  }
  return (x + x);
}

/// 7. let-bound match in monadic context
std::string LetMatchType::let_match_monadic(bool b) {
  std::string msg;
  if (b) {
    msg = "yes";
  } else {
    msg = "no";
  }
  std::cout << msg << '\n';
  return msg;
}

std::pair<uint64_t, uint64_t>
LetMatchType::direction_offset(LetMatchType::Direction d) {
  uint64_t dx = [&]() {
    switch (d) {
    case Direction::EAST: {
      return UINT64_C(1);
    }
    case Direction::WEST: {
      return UINT64_C(2);
    }
    default: {
      return UINT64_C(0);
    }
    }
  }();
  uint64_t dy = [&]() {
    switch (d) {
    case Direction::NORTH: {
      return UINT64_C(1);
    }
    case Direction::SOUTH: {
      return UINT64_C(2);
    }
    default: {
      return UINT64_C(0);
    }
    }
  }();
  return std::make_pair(dx, dy);
}
