#ifndef INCLUDED_RECORD_DEFAULTS
#define INCLUDED_RECORD_DEFAULTS

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct RecordDefaults {
  struct Config {
    unsigned int cfg_width;
    unsigned int cfg_height;
    unsigned int cfg_depth;
    bool cfg_debug;

    __attribute__((pure)) Config *operator->() { return this; }

    __attribute__((pure)) const Config *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Config clone() const {
      return Config{(*(this)).cfg_width, (*(this)).cfg_height,
                    (*(this)).cfg_depth, (*(this)).cfg_debug};
    }
  };

  static inline const Config default_config = Config{80u, 24u, 1u, false};
  __attribute__((pure)) static Config set_width(unsigned int w,
                                                const Config &c);
  __attribute__((pure)) static Config set_debug(bool d, const Config &c);

  struct Point {
    unsigned int px;
    unsigned int py;

    __attribute__((pure)) Point *operator->() { return this; }

    __attribute__((pure)) const Point *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Point clone() const {
      return Point{(*(this)).px, (*(this)).py};
    }
  };

  struct Rect {
    Point origin;
    Point extent;

    __attribute__((pure)) Rect *operator->() { return this; }

    __attribute__((pure)) const Rect *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Rect clone() const {
      return Rect{(*(this)).origin.clone(), (*(this)).extent.clone()};
    }
  };

  __attribute__((pure)) static unsigned int rect_area(const Rect &r);
  __attribute__((pure)) static Rect make_rect(unsigned int x, unsigned int y,
                                              unsigned int w, unsigned int h);
  __attribute__((pure)) static unsigned int total_cells(const Config &c);
  static inline const unsigned int test_default_width =
      default_config.cfg_width;
  static inline const bool test_default_debug = default_config.cfg_debug;
  static inline const unsigned int test_cells = total_cells(default_config);
  static inline const unsigned int test_modified =
      total_cells(set_width(120u, set_debug(true, default_config)));
  static inline const unsigned int test_rect_area =
      rect_area(make_rect(0u, 0u, 10u, 5u));
};

#endif // INCLUDED_RECORD_DEFAULTS
