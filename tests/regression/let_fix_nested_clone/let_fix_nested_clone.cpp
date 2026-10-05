#include "let_fix_nested_clone.h"

uint64_t LetFixNestedClone::sum_nested(const List<List<uint64_t>> &ll) {
  auto outer = [](const List<List<uint64_t>> &xss, uint64_t acc) -> uint64_t {
    uint64_t _loop_acc = std::move(acc);
    const List<List<uint64_t>> *_loop_xss = &xss;
    while (true) {
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
              _loop_xss->v())) {
        return _loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(_loop_xss->v());
        auto inner_impl = [](auto &_self_inner, const List<uint64_t> &ys,
                             uint64_t a) -> uint64_t {
          if (std::holds_alternative<typename List<uint64_t>::Nil>(ys.v())) {
            return a;
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(ys.v());
            return _self_inner(_self_inner, *a10, (a + a00));
          }
        };
        auto inner = [&](const List<uint64_t> &ys, uint64_t a) -> uint64_t {
          return inner_impl(inner_impl, ys, a);
        };
        _loop_acc = (inner(a0, UINT64_C(0)) + _loop_acc);
        _loop_xss = crane_raw(a1);
      }
    }
  };
  return outer(ll, UINT64_C(0));
}

uint64_t LetFixNestedClone::count_nested(const List<List<uint64_t>> &ll) {
  auto outer = [](const List<List<uint64_t>> &xss, uint64_t acc) -> uint64_t {
    uint64_t _loop_acc = std::move(acc);
    const List<List<uint64_t>> *_loop_xss = &xss;
    while (true) {
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
              _loop_xss->v())) {
        return _loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(_loop_xss->v());
        auto inner_impl = [](auto &_self_inner, const List<uint64_t> &ys,
                             uint64_t n) -> uint64_t {
          if (std::holds_alternative<typename List<uint64_t>::Nil>(ys.v())) {
            return n;
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(ys.v());
            return _self_inner(_self_inner, *a10, (UINT64_C(1) + n));
          }
        };
        auto inner = [&](const List<uint64_t> &ys, uint64_t n) -> uint64_t {
          return inner_impl(inner_impl, ys, n);
        };
        _loop_acc = (inner(a0, UINT64_C(0)) + _loop_acc);
        _loop_xss = crane_raw(a1);
      }
    }
  };
  return outer(ll, UINT64_C(0));
}
