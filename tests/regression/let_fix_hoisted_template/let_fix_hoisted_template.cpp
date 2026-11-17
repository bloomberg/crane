#include "let_fix_hoisted_template.h"

List<uint64_t> LetFixHoistedTemplate::reverse_onto(const List<uint64_t> &l) {
  {
    const List<uint64_t> &_lc1_xs = l;
    List<uint64_t> _lc1_acc = List<uint64_t>::nil();
    List<uint64_t> _lc1_loop_acc = std::move(_lc1_acc);
    const List<uint64_t> *_lc1_loop_xs = &_lc1_xs;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _lc1_loop_xs->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_lc1_loop_xs->v());
        _lc1_loop_acc = List<uint64_t>::cons(a0, std::move(_lc1_loop_acc));
        _lc1_loop_xs = crane_raw(a1);
      }
    }
  }
}
