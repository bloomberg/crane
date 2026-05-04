#include "record_defaults.h"

RecordDefaults::Config
RecordDefaults::set_width(const unsigned int w,
                          const RecordDefaults::Config &c) {
  return Config{w, c.cfg_height, c.cfg_depth, c.cfg_debug};
}

RecordDefaults::Config
RecordDefaults::set_debug(const bool d, const RecordDefaults::Config &c) {
  return Config{c.cfg_width, c.cfg_height, c.cfg_depth, d};
}

unsigned int RecordDefaults::rect_area(const RecordDefaults::Rect &r) {
  return (r.extent.px * r.extent.py);
}

RecordDefaults::Rect RecordDefaults::make_rect(const unsigned int x,
                                               const unsigned int y,
                                               const unsigned int w,
                                               const unsigned int h) {
  return Rect{Point{x, y}, Point{w, h}};
}

unsigned int RecordDefaults::total_cells(const RecordDefaults::Config &c) {
  return ((c.cfg_width * c.cfg_height) * c.cfg_depth);
}
