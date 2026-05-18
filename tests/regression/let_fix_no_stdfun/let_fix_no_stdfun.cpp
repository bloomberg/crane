#include "let_fix_no_stdfun.h"

uint64_t LetFixNoStdfun::sum_list(const List<uint64_t> &l) {
  auto go_impl = [](auto &_self_go, const List<uint64_t> &xs,
                    uint64_t acc) -> uint64_t {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
      return acc;
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
      return _self_go(_self_go, *a1, (acc + a0));
    }
  };
  auto go = [&](const List<uint64_t> &xs, uint64_t acc) -> uint64_t {
    return go_impl(go_impl, xs, acc);
  };
  return go(l, UINT64_C(0));
}

uint64_t LetFixNoStdfun::flat_map_sum(const List<List<uint64_t>> &xss) {
  if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(xss.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename List<List<uint64_t>>::Cons>(xss.v());
    auto inner_sum_impl = [](auto &_self_inner_sum, const List<uint64_t> &ys,
                             uint64_t acc) -> uint64_t {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(ys.v())) {
        return acc;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(ys.v());
        return _self_inner_sum(_self_inner_sum, *a10, (acc + a00));
      }
    };
    auto inner_sum = [&](const List<uint64_t> &ys, uint64_t acc) -> uint64_t {
      return inner_sum_impl(inner_sum_impl, ys, acc);
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
