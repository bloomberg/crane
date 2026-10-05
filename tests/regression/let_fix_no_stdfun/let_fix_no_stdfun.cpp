#include "let_fix_no_stdfun.h"

uint64_t LetFixNoStdfun::sum_list(const List<uint64_t> &l) {
  {
    const List<uint64_t> &_lc1_xs = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = std::move(_lc1_acc);
    const List<uint64_t> *_lc1_loop_xs = &_lc1_xs;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _lc1_loop_xs->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_lc1_loop_xs->v());
        _lc1_loop_acc = (_lc1_loop_acc + a0);
        _lc1_loop_xs = crane_raw(a1);
      }
    }
  }
}

uint64_t LetFixNoStdfun::flat_map_sum(const List<List<uint64_t>> &xss) {
  if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(xss.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename List<List<uint64_t>>::Cons>(xss.v());
    auto inner_sum = [](const List<uint64_t> &ys, uint64_t acc) -> uint64_t {
      uint64_t _loop_acc = std::move(acc);
      const List<uint64_t> *_loop_ys = &ys;
      while (true) {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(
                _loop_ys->v())) {
          return _loop_acc;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_loop_ys->v());
          _loop_acc = (_loop_acc + a00);
          _loop_ys = crane_raw(a10);
        }
      }
    };
    return (inner_sum(a0, UINT64_C(0)) + flat_map_sum(*a1));
  }
}

List<uint64_t> LetFixNoStdfun::flatten(const List<List<uint64_t>> &xss) {
  if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(xss.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] =
        std::get<typename List<List<uint64_t>>::Cons>(xss.v());
    auto inner_impl = [&](auto &_self_inner,
                          const List<uint64_t> &ys) -> List<uint64_t> {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(ys.v())) {
        return flatten(*a1);
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(ys.v());
        return List<uint64_t>::cons(a00, _self_inner(_self_inner, *a10));
      }
    };
    auto inner = [&](const List<uint64_t> &ys) -> List<uint64_t> {
      return inner_impl(inner_impl, ys);
    };
    return inner(a0);
  }
}
