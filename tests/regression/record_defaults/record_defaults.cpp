#include <record_defaults.h>

#include <memory>
#include <optional>
#include <type_traits>

__attribute__((pure)) RecordDefaults::Config
RecordDefaults::set_width(unsigned int w, const RecordDefaults::Config &c) {
  return Config{w, c.cfg_height, c.cfg_depth, c.cfg_debug};
}

__attribute__((pure)) RecordDefaults::Config
RecordDefaults::set_debug(bool d, const RecordDefaults::Config &c) {
  return Config{c.cfg_width, c.cfg_height, c.cfg_depth, d};
}

__attribute__((pure)) unsigned int
RecordDefaults::rect_area(const RecordDefaults::Rect &r) {
  return (r.extent.px * r.extent.py);
}

__attribute__((pure)) RecordDefaults::Rect
RecordDefaults::make_rect(unsigned int x, unsigned int y, unsigned int w,
                          unsigned int h) {
  return Rect{Point{x, y}, Point{w, h}};
}

__attribute__((pure)) unsigned int
RecordDefaults::total_cells(const RecordDefaults::Config &c) {
  return ((c.cfg_width * c.cfg_height) * c.cfg_depth);
}
