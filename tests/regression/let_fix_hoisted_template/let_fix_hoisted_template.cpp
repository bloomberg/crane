#include "let_fix_hoisted_template.h"

List<uint64_t> LetFixHoistedTemplate::reverse_onto(const List<uint64_t> &l) {
  auto go_impl = [](auto &_self_go, const List<uint64_t> &xs,
                    List<uint64_t> acc) -> List<uint64_t> {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
      return acc;
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
      return _self_go(_self_go, *a1, List<uint64_t>::cons(a0, std::move(acc)));
    }
  };
  auto go = [&](const List<uint64_t> &xs,
                List<uint64_t> acc) -> List<uint64_t> {
    return go_impl(go_impl, xs, acc);
  };
  return go(l, List<uint64_t>::nil());
}
