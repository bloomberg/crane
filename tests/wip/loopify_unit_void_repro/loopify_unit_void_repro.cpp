#include <loopify_unit_void_repro.h>

void LoopifyUnitVoidRepro::loop(unsigned int x, unsigned int y,
                                const List<bool> &cells) {
  const List<bool> *_loop_cells = &cells;
  unsigned int _loop_x = std::move(x);
  while (true) {
    if (std::holds_alternative<typename List<bool>::Nil>(_loop_cells->v())) {
      return;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<bool>::Cons>(_loop_cells->v());
      [&]() -> void {
        if (d_a0) {
          ((void)_loop_x, (void)y);
          return;
        } else {
          ((void)_loop_x, (void)y);
          return;
        }
      }();
      const List<bool> *_next_cells = d_a1.get();
      unsigned int _next_x = (_loop_x + cell_size);
      _loop_cells = std::move(_next_cells);
      _loop_x = std::move(_next_x);
    }
  }
  return;
}

int LoopifyUnitVoidRepro::run() {
  loop(0u, 0u,
       List<bool>::cons(true, List<bool>::cons(false, List<bool>::nil())));
  return 0;
}
