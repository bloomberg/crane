#include <let_match_type2.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// 1. Match returning bool — should be fine
__attribute__((pure)) bool LetMatchType2::let_match_bool(const unsigned int n) {
  bool b;
  if (n <= 0) {
    b = true;
  } else {
    unsigned int _x = n - 1;
    b = false;
  }
  return !(b);
}

/// 2. Match returning pair — might trigger std::any
__attribute__((pure)) unsigned int LetMatchType2::let_match_pair(const bool b) {
  std::pair<unsigned int, unsigned int> p;
  if (b) {
    p = std::make_pair(1u, 2u);
  } else {
    p = std::make_pair(3u, 4u);
  }
  return (p.first + p.second);
}

/// 3. Match returning list — might trigger std::any
std::shared_ptr<List<unsigned int>>
LetMatchType2::let_match_list(const bool b) {
  if (b) {
    return List<unsigned int>::cons(1u, List<unsigned int>::nil());
  } else {
    return List<unsigned int>::nil();
  }
}

/// 4. Match returning option — might trigger std::any
__attribute__((pure)) std::optional<unsigned int>
LetMatchType2::let_match_opt(const bool b) {
  if (b) {
    return std::make_optional<unsigned int>(1u);
  } else {
    return std::optional<unsigned int>();
  }
}

/// 5. Cascading let-matches all returning nat — should be fine
__attribute__((pure)) unsigned int
LetMatchType2::cascading_nat(const bool a, const bool b, const bool c) {
  unsigned int x;
  if (a) {
    x = 10u;
  } else {
    x = 0u;
  }
  unsigned int y;
  if (b) {
    y = 5u;
  } else {
    y = 0u;
  }
  unsigned int z;
  if (c) {
    z = 1u;
  } else {
    z = 0u;
  }
  return ((x + y) + z);
}

/// 6. Match returning function type
__attribute__((pure)) unsigned int LetMatchType2::let_match_fun(const bool b) {
  unsigned int x = 5u;
  if (b) {
    return (x + 1);
  } else {
    return x;
  }
}

/// 7. Match result used in another match
__attribute__((pure)) unsigned int
LetMatchType2::match_of_match(const unsigned int n) {
  unsigned int x;
  if (n <= 0) {
    x = 1u;
  } else {
    unsigned int _x = n - 1;
    x = 2u;
  }
  if (x <= 0) {
    return 100u;
  } else {
    unsigned int n0 = x - 1;
    if (n0 <= 0) {
      return 200u;
    } else {
      unsigned int _x = n0 - 1;
      return 300u;
    }
  }
}

/// 8. let-bound match where arms have bindings
__attribute__((pure)) unsigned int
LetMatchType2::let_match_bindings(const unsigned int n) {
  unsigned int x;
  if (n <= 0) {
    x = 0u;
  } else {
    unsigned int m = n - 1;
    x = (m + 1u);
  }
  return (x + x);
}
