#ifndef INCLUDED_RECORD_DEFAULTS
#define INCLUDED_RECORD_DEFAULTS

#include <cstdint>

struct RecordDefaults {
  struct Config {
    uint64_t cfg_width;
    uint64_t cfg_height;
    uint64_t cfg_depth;
    bool cfg_debug;
  };

  static inline const Config default_config =
      Config{UINT64_C(80), UINT64_C(24), UINT64_C(1), false};
  static Config set_width(uint64_t w, const Config &c);
  static Config set_debug(bool d, const Config &c);

  struct Point {
    uint64_t px;
    uint64_t py;
  };

  struct Rect {
    Point origin;
    Point extent;
  };

  static uint64_t rect_area(const Rect &r);
  static Rect make_rect(uint64_t x, uint64_t y, uint64_t w, uint64_t h);
  static uint64_t total_cells(const Config &c);
  static constexpr uint64_t test_default_width = UINT64_C(80);
  static constexpr bool test_default_debug = false;
  static constexpr uint64_t test_cells = UINT64_C(1920);
  static constexpr uint64_t test_modified = UINT64_C(2880);
  static constexpr uint64_t test_rect_area = UINT64_C(50);
};

#endif // INCLUDED_RECORD_DEFAULTS
