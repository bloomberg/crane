#include "let_fix.h"

uint64_t LetFix::local_sum(const List<uint64_t> &l) {
  auto go = [](uint64_t acc, const List<uint64_t> &xs) -> uint64_t {
    const List<uint64_t> *_loop_xs = &xs;
    uint64_t _loop_acc = std::move(acc);
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_xs->v())) {
        return _loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_xs->v());
        _loop_xs = crane_raw(a1);
        _loop_acc = (_loop_acc + a0);
      }
    }
  };
  return go(UINT64_C(0), l);
}

List<uint64_t> LetFix::local_flatten(const List<List<uint64_t>> &xss) {
  if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(xss.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] =
        std::get<typename List<List<uint64_t>>::Cons>(xss.v());
    auto inner_impl = [&](auto &_self_inner,
                          const List<uint64_t> &ys) -> List<uint64_t> {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(ys.v())) {
        return local_flatten(*a1);
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

bool LetFix::local_mem(uint64_t n, const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return false;
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    if (a0 == n) {
      return true;
    } else {
      return local_mem(n, *a1);
    }
  }
}
