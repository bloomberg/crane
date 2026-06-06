#ifndef INCLUDED_VALID_LAYOUT_WINDOW
#define INCLUDED_VALID_LAYOUT_WINDOW

struct ValidLayoutWindow {
  struct layout {
    uint64_t base_addr;
    uint64_t code_size;
  };

  static bool valid_layoutb(const layout &l);
  static inline const uint64_t t =
      ((valid_layoutb(layout{UINT64_C(128), UINT64_C(256)}) ? UINT64_C(1)
                                                            : UINT64_C(0)) +
       (valid_layoutb(layout{UINT64_C(4090), UINT64_C(20)}) ? UINT64_C(1)
                                                            : UINT64_C(0)));
};

#endif // INCLUDED_VALID_LAYOUT_WINDOW
