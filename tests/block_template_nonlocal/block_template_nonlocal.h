#ifndef INCLUDED_BLOCK_TEMPLATE_NONLOCAL
#define INCLUDED_BLOCK_TEMPLATE_NONLOCAL

#include <iostream>

struct BlockTemplateNonlocal {
  static inline const uint64_t pure_block_let = ([]() -> uint64_t {
    uint64_t _r;
    std::cin >> _r;
    return _r;
  }() + UINT64_C(42));
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
