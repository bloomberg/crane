#include "let_match_type2.h"

/// 1. Match returning bool — should be fine
bool LetMatchType2::let_match_bool(uint64_t n) {
  bool b;
  if (n <= 0) {
    b = true;
  } else {
    uint64_t _x = n - 1;
    b = false;
  }
  return !(b);
}

/// 2. Match returning pair — might trigger std::any
uint64_t LetMatchType2::let_match_pair(bool b) {
  std::pair<uint64_t, uint64_t> p;
  if (b) {
    p = std::make_pair(UINT64_C(1), UINT64_C(2));
  } else {
    p = std::make_pair(UINT64_C(3), UINT64_C(4));
  }
  return (p.first + p.second);
}

/// 3. Match returning list — might trigger std::any
List<uint64_t> LetMatchType2::let_match_list(bool b) {
  if (b) {
    return List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil());
  } else {
    return List<uint64_t>::nil();
  }
}

/// 4. Match returning option — might trigger std::any
std::optional<uint64_t> LetMatchType2::let_match_opt(bool b) {
  if (b) {
    return std::make_optional<uint64_t>(UINT64_C(1));
  } else {
    return std::optional<uint64_t>();
  }
}

/// 5. Cascading let-matches all returning nat — should be fine
uint64_t LetMatchType2::cascading_nat(bool a, bool b, bool c) {
  uint64_t x;
  if (a) {
    x = UINT64_C(10);
  } else {
    x = UINT64_C(0);
  }
  uint64_t y;
  if (b) {
    y = UINT64_C(5);
  } else {
    y = UINT64_C(0);
  }
  uint64_t z;
  if (c) {
    z = UINT64_C(1);
  } else {
    z = UINT64_C(0);
  }
  return ((x + y) + z);
}

/// 6. Match returning function type
uint64_t LetMatchType2::let_match_fun(bool b) {
  uint64_t x = UINT64_C(5);
  if (b) {
    return (x + 1);
  } else {
    return x;
  }
}

/// 7. Match result used in another match
uint64_t LetMatchType2::match_of_match(uint64_t n) {
  uint64_t x;
  if (n <= 0) {
    x = UINT64_C(1);
  } else {
    uint64_t _x = n - 1;
    x = UINT64_C(2);
  }
  if (x <= 0) {
    return UINT64_C(100);
  } else {
    uint64_t n0 = x - 1;
    if (n0 <= 0) {
      return UINT64_C(200);
    } else {
      uint64_t _x = n0 - 1;
      return UINT64_C(300);
    }
  }
}

/// 8. let-bound match where arms have bindings
uint64_t LetMatchType2::let_match_bindings(uint64_t n) {
  uint64_t x;
  if (n <= 0) {
    x = UINT64_C(0);
  } else {
    uint64_t m = n - 1;
    x = (m + UINT64_C(1));
  }
  return (x + x);
}
