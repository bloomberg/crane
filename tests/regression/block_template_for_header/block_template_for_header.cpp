#include "block_template_for_header.h"

uint64_t BlockTemplateForHeader::next_after(uint64_t n) {
  return ([&]() -> uint64_t {
    uint64_t _r;
    for (unsigned int _i = 0;; ++_i) {
      if (_i >= n) {
        _r = _i;
        break;
      }
    };
    return _r;
  }() + UINT64_C(1));
}
