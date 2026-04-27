#include <let_match_type.h>

/// 1. let-bound bool match returning nat
__attribute__((pure)) unsigned int LetMatchType::let_match_nat(const bool &b) {
  unsigned int x;
  if (b) {
    x = 1u;
  } else {
    x = 0u;
  }
  return (x + x);
}

/// 2. let-bound nat match returning string — TRIGGERS std::any bug
__attribute__((pure)) std::string
LetMatchType::let_match_string(const unsigned int &n) {
  std::string s;
  if (n <= 0) {
    s = "zero";
  } else {
    unsigned int _x = n - 1;
    s = "nonzero";
  }
  return s + s;
}

/// 3. let-bound option match
__attribute__((pure)) unsigned int
LetMatchType::let_match_option(const std::optional<unsigned int> &o) {
  unsigned int x;
  if (o.has_value()) {
    const unsigned int &n = *o;
    x = n;
  } else {
    x = 0u;
  }
  return (x + 1u);
}

/// 4. let-bound nested bool match
__attribute__((pure)) unsigned int
LetMatchType::let_nested_bool(const bool &a, const bool &b) {
  if (a) {
    if (b) {
      return 3u;
    } else {
      return 2u;
    }
  } else {
    if (b) {
      return 1u;
    } else {
      return 0u;
    }
  }
}

/// 5. Multiple let-bound matches
__attribute__((pure)) unsigned int
LetMatchType::multi_let_match(const bool &a, const bool &b) {
  unsigned int x;
  if (a) {
    x = 10u;
  } else {
    x = 0u;
  }
  unsigned int y;
  if (b) {
    y = 1u;
  } else {
    y = 0u;
  }
  return (x + y);
}

/// 6. let-bound match used in function argument
__attribute__((pure)) unsigned int
LetMatchType::let_match_in_arg(const unsigned int &n) {
  unsigned int x;
  if (n <= 0) {
    x = 0u;
  } else {
    unsigned int n_ = n - 1;
    x = n_;
  }
  return (x + x);
}

/// 7. let-bound match in monadic context
std::string LetMatchType::let_match_monadic(const bool &b) {
  std::string msg;
  if (b) {
    msg = "yes";
  } else {
    msg = "no";
  }
  std::cout << msg << '\n';
  return msg;
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
LetMatchType::direction_offset(const LetMatchType::Direction d) {
  unsigned int dx = [&]() {
    switch (d) {
    case Direction::e_EAST: {
      return 1u;
    }
    case Direction::e_WEST: {
      return 2u;
    }
    default: {
      return 0u;
    }
    }
  }();
  unsigned int dy = [&]() {
    switch (d) {
    case Direction::e_NORTH: {
      return 1u;
    }
    case Direction::e_SOUTH: {
      return 2u;
    }
    default: {
      return 0u;
    }
    }
  }();
  return std::make_pair(dx, dy);
}
