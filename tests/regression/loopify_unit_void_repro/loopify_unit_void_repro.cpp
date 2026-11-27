#include "loopify_unit_void_repro.h"

void LoopifyUnitVoidRepro::loop(uint64_t x, uint64_t y,
                                const List<bool> &cells) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<bool> *_loop_cells = &cells;
  while (true) {
    if (std::holds_alternative<typename List<bool>::Nil>(_loop_cells->v())) {
      return;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<bool>::Cons>(_loop_cells->v());
      [&]() -> void {
        if (a0) {
          ((void)x, (void)y);
          return;
        } else {
          ((void)x, (void)y);
          return;
        }
      }();
      _loop_cells = crane_raw(a1);
      x = (x + cell_size);
    }
  }
}

int LoopifyUnitVoidRepro::run() {
  loop(UINT64_C(0), UINT64_C(0),
       List<bool>::cons(true, List<bool>::cons(false, List<bool>::nil())));
  return 0;
}
