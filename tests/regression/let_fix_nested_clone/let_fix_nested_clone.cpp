#include "let_fix_nested_clone.h"

uint64_t LetFixNestedClone::sum_nested(const List<List<uint64_t>> &ll) {
  {
    const List<List<uint64_t>> &_lc1_xss = ll;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const List<List<uint64_t>> *_lc1_loop_xss = &_lc1_xss;
    while (true) {
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
              _lc1_loop_xss->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(_lc1_loop_xss->v());
        auto inner = [](const List<uint64_t> &ys, uint64_t a) -> uint64_t {
          uint64_t _loop_a = a;
          const List<uint64_t> *_loop_ys = &ys;
          while (true) {
            if (std::holds_alternative<typename List<uint64_t>::Nil>(
                    _loop_ys->v())) {
              return _loop_a;
            } else {
              const auto &[a00, a10] =
                  std::get<typename List<uint64_t>::Cons>(_loop_ys->v());
              _loop_a = (_loop_a + a00);
              _loop_ys = crane_raw(a10);
            }
          }
        };
        _lc1_loop_acc = (inner(a0, UINT64_C(0)) + _lc1_loop_acc);
        _lc1_loop_xss = crane_raw(a1);
      }
    }
  }
}

uint64_t LetFixNestedClone::count_nested(const List<List<uint64_t>> &ll) {
  {
    const List<List<uint64_t>> &_lc1_xss = ll;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const List<List<uint64_t>> *_lc1_loop_xss = &_lc1_xss;
    while (true) {
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
              _lc1_loop_xss->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(_lc1_loop_xss->v());
        auto inner = [](const List<uint64_t> &ys, uint64_t n) -> uint64_t {
          uint64_t _loop_n = n;
          const List<uint64_t> *_loop_ys = &ys;
          while (true) {
            if (std::holds_alternative<typename List<uint64_t>::Nil>(
                    _loop_ys->v())) {
              return _loop_n;
            } else {
              const auto &[a00, a10] =
                  std::get<typename List<uint64_t>::Cons>(_loop_ys->v());
              _loop_n = (UINT64_C(1) + _loop_n);
              _loop_ys = crane_raw(a10);
            }
          }
        };
        _lc1_loop_acc = (inner(a0, UINT64_C(0)) + _lc1_loop_acc);
        _lc1_loop_xss = crane_raw(a1);
      }
    }
  }
}
