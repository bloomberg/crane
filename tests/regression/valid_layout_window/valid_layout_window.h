#ifndef INCLUDED_VALID_LAYOUT_WINDOW
#define INCLUDED_VALID_LAYOUT_WINDOW

#include <memory>
#include <optional>
#include <type_traits>

struct ValidLayoutWindow {
  struct layout {
    unsigned int base_addr;
    unsigned int code_size;

    // ACCESSORS
    layout clone() const {
      return layout{(*(this)).base_addr, (*(this)).code_size};
    }
  };

  static bool valid_layoutb(const layout &l);
  static inline const unsigned int t =
      ((valid_layoutb(layout{128u, 256u}) ? 1u : 0u) +
       (valid_layoutb(layout{4090u, 20u}) ? 1u : 0u));
};

#endif // INCLUDED_VALID_LAYOUT_WINDOW
