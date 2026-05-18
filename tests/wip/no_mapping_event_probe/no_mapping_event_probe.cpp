#include "no_mapping_event_probe.h"

void NoMappingEventProbe::draw_hidden_tile(uint64_t x, uint64_t y) {
  {
    reproE::hidden(x, y);
    return;
  }
}

void NoMappingEventProbe::draw_revealed_tile(uint64_t x, uint64_t y) {
  {
    reproE::revealed(x, y);
    return;
  }
}

void NoMappingEventProbe::loop(uint64_t x, uint64_t y,
                               const List<bool> &cells) {
  if (std::holds_alternative<typename List<bool>::Nil>(cells.v())) {
    return;
  } else {
    const auto &[a0, a1] = std::get<typename List<bool>::Cons>(cells.v());
    [&]() -> void {
      if (a0) {
        draw_revealed_tile(x, y);
        return;
      } else {
        draw_hidden_tile(x, y);
        return;
      }
    }();
    loop((x + cell_size), y, *a1);
    return;
  }
}
