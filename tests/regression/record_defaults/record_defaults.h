#ifndef INCLUDED_RECORD_DEFAULTS
#define INCLUDED_RECORD_DEFAULTS

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct RecordDefaults {
  struct Config {
    unsigned int cfg_width;
    unsigned int cfg_height;
    unsigned int cfg_depth;
    bool cfg_debug;
  };

  static inline const std::shared_ptr<Config> default_config =
      std::make_shared<Config>(Config{80u, 24u, 1u, false});
  static std::shared_ptr<Config> set_width(const unsigned int w,
                                           std::shared_ptr<Config> c);
  static std::shared_ptr<Config> set_debug(const bool d,
                                           std::shared_ptr<Config> c);

  struct Point {
    unsigned int px;
    unsigned int py;
  };

  struct Rect {
    std::shared_ptr<Point> origin;
    std::shared_ptr<Point> extent;
  };

  __attribute__((pure)) static unsigned int
  rect_area(const std::shared_ptr<Rect> &r);
  static std::shared_ptr<Rect> make_rect(const unsigned int x,
                                         const unsigned int y,
                                         const unsigned int w,
                                         const unsigned int h);
  __attribute__((pure)) static unsigned int
  total_cells(const std::shared_ptr<Config> &c);
  static inline const unsigned int test_default_width =
      default_config->cfg_width;
  static inline const bool test_default_debug = default_config->cfg_debug;
  static inline const unsigned int test_cells = total_cells(default_config);
  static inline const unsigned int test_modified =
      total_cells(set_width(120u, set_debug(true, default_config)));
  static inline const unsigned int test_rect_area =
      rect_area(make_rect(0u, 0u, 10u, 5u));
};

#endif // INCLUDED_RECORD_DEFAULTS
