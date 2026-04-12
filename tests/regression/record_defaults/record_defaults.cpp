#include <record_defaults.h>

#include <memory>
#include <type_traits>

std::shared_ptr<RecordDefaults::Config>
RecordDefaults::set_width(const unsigned int w,
                          const std::shared_ptr<RecordDefaults::Config> &c) {
  return std::make_shared<RecordDefaults::Config>(
      Config{w, c->cfg_height, c->cfg_depth, c->cfg_debug});
}

std::shared_ptr<RecordDefaults::Config>
RecordDefaults::set_debug(const bool d,
                          const std::shared_ptr<RecordDefaults::Config> &c) {
  return std::make_shared<RecordDefaults::Config>(
      Config{c->cfg_width, c->cfg_height, c->cfg_depth, d});
}

__attribute__((pure)) unsigned int
RecordDefaults::rect_area(const std::shared_ptr<RecordDefaults::Rect> &r) {
  return (r->extent->px * r->extent->py);
}

std::shared_ptr<RecordDefaults::Rect>
RecordDefaults::make_rect(const unsigned int x, const unsigned int y,
                          const unsigned int w, const unsigned int h) {
  return std::make_shared<RecordDefaults::Rect>(
      Rect{std::make_shared<RecordDefaults::Point>(Point{x, y}),
           std::make_shared<RecordDefaults::Point>(Point{w, h})});
}

__attribute__((pure)) unsigned int
RecordDefaults::total_cells(const std::shared_ptr<RecordDefaults::Config> &c) {
  return ((c->cfg_width * c->cfg_height) * c->cfg_depth);
}
