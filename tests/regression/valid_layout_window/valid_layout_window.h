#ifndef INCLUDED_VALID_LAYOUT_WINDOW
#define INCLUDED_VALID_LAYOUT_WINDOW

#include <cstdint>

struct ValidLayoutWindow {
  struct layout {
    uint64_t base_addr;
    uint64_t code_size;
  };

  static bool valid_layoutb(const layout &l);
  static constexpr uint64_t t = UINT64_C(1);
};

#endif // INCLUDED_VALID_LAYOUT_WINDOW
