#ifndef INCLUDED_BLOCK_TEMPLATE_NONLOCAL
#define INCLUDED_BLOCK_TEMPLATE_NONLOCAL

#include <iostream>

struct BlockTemplateNonlocal {
  /// Block template in pure let binding — compiled to static inline initializer
  /// with an expression-position IIFE.
  /// Generates: static inline const unsigned int x = (&() -> unsigned int { ...
  /// }() + 42u); Bug: & is invalid in non-local lambda. Should be ().
  static inline const uint64_t pure_block_let = ([]() -> uint64_t {
    uint64_t _r;
    std::cin >> _r;
    return _r;
  }() + UINT64_C(42));
  /// Two pure block templates in same expression
  static inline const uint64_t two_pure_blocks = ([]() -> uint64_t {
    uint64_t _r;
    std::cin >> _r;
    return _r;
  }() + []() -> uint64_t {
    uint64_t _r;
    std::cin >> _r;
    return _r;
  }());
};

#endif // INCLUDED_BLOCK_TEMPLATE_NONLOCAL
