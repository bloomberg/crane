#include <no_mapping_event_probe.h>

void NoMappingEventProbe::draw_hidden_tile(unsigned int x, unsigned int y) {
  {
    reproE::hidden(x, y);
    return;
  }
}

void NoMappingEventProbe::draw_revealed_tile(unsigned int x, unsigned int y) {
  {
    reproE::revealed(x, y);
    return;
  }
}

void NoMappingEventProbe::loop(unsigned int x, unsigned int y,
                               const List<bool> &cells) {
  if (std::holds_alternative<typename List<bool>::Nil>(cells.v())) {
    return;
  } else {
    const auto &[d_a0, d_a1] = std::get<typename List<bool>::Cons>(cells.v());
    [&]() -> void {
      if (d_a0) {
        draw_revealed_tile(x, y);
        return;
      } else {
        draw_hidden_tile(x, y);
        return;
      }
    }();
    loop((x + cell_size), y, *(d_a1));
    return;
  }
}
