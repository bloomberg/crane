#include "record_defaults.h"

RecordDefaults::Config
RecordDefaults::set_width(uint64_t w, const RecordDefaults::Config &c) {
  return Config{w, c.cfg_height, c.cfg_depth, c.cfg_debug};
}

RecordDefaults::Config
RecordDefaults::set_debug(bool d, const RecordDefaults::Config &c) {
  return Config{c.cfg_width, c.cfg_height, c.cfg_depth, d};
}

uint64_t RecordDefaults::rect_area(const RecordDefaults::Rect &r) {
  return (r.extent.px * r.extent.py);
}

RecordDefaults::Rect RecordDefaults::make_rect(uint64_t x, uint64_t y,
                                               uint64_t w, uint64_t h) {
  return Rect{Point{x, y}, Point{w, h}};
}

uint64_t RecordDefaults::total_cells(const RecordDefaults::Config &c) {
  return ((c.cfg_width * c.cfg_height) * c.cfg_depth);
}
