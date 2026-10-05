#include "let_fix_hoisted_template.h"

List<uint64_t> LetFixHoistedTemplate::reverse_onto(const List<uint64_t> &l) {
  auto go = [](const List<uint64_t> &xs, List<uint64_t> acc) -> List<uint64_t> {
    List<uint64_t> _loop_acc = std::move(acc);
    const List<uint64_t> *_loop_xs = &xs;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_xs->v())) {
        return _loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_xs->v());
        _loop_acc = List<uint64_t>::cons(a0, std::move(_loop_acc));
        _loop_xs = crane_raw(a1);
      }
    }
  };
  return go(l, List<uint64_t>::nil());
}
