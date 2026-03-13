#include <record_defaults.h>

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

std::shared_ptr<RecordDefaults::Config>
RecordDefaults::set_width(const unsigned int w,
                          std::shared_ptr<RecordDefaults::Config> c) {
  return std::make_shared<RecordDefaults::Config>(
      Config{std::move(w), c->cfg_height, c->cfg_depth, c->cfg_debug});
}

std::shared_ptr<RecordDefaults::Config>
RecordDefaults::set_debug(const bool d,
                          std::shared_ptr<RecordDefaults::Config> c) {
  return std::make_shared<RecordDefaults::Config>(
      Config{c->cfg_width, c->cfg_height, c->cfg_depth, std::move(d)});
}

__attribute__((pure)) unsigned int
RecordDefaults::rect_area(const std::shared_ptr<RecordDefaults::Rect> &r) {
  return (r->extent->px * r->extent->py);
}

std::shared_ptr<RecordDefaults::Rect>
RecordDefaults::make_rect(const unsigned int x, const unsigned int y,
                          const unsigned int w, const unsigned int h) {
  return std::make_shared<RecordDefaults::Rect>(
      Rect{std::make_shared<RecordDefaults::Point>(
               Point{std::move(x), std::move(y)}),
           std::make_shared<RecordDefaults::Point>(
               Point{std::move(w), std::move(h)})});
}

__attribute__((pure)) unsigned int
RecordDefaults::total_cells(const std::shared_ptr<RecordDefaults::Config> &c) {
  return ((c->cfg_width * c->cfg_height) * c->cfg_depth);
}
