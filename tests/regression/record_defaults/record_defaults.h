#ifndef INCLUDED_RECORD_DEFAULTS
#define INCLUDED_RECORD_DEFAULTS

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
  static inline const uint64_t test_default_width = default_config.cfg_width;
  static inline const bool test_default_debug = default_config.cfg_debug;
  static inline const uint64_t test_cells = total_cells(default_config);
  static inline const uint64_t test_modified =
      total_cells(set_width(UINT64_C(120), set_debug(true, default_config)));
  static inline const uint64_t test_rect_area =
      rect_area(make_rect(UINT64_C(0), UINT64_C(0), UINT64_C(10), UINT64_C(5)));
};

#endif // INCLUDED_RECORD_DEFAULTS
