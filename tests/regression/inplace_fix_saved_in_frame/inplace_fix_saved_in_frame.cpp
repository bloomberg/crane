#include "inplace_fix_saved_in_frame.h"

List<List<uint64_t>>
InplaceFixSavedInFrame::insert_shift(uint64_t x, const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of insert_shift: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_insert_shift_in_Cons {
    List<uint64_t> l;
    uint64_t k;
    crane::fn<List<List<uint64_t>>(List<List<uint64_t>>)> map_k;
  };

  using _frame = std::variant<_call, _after_insert_shift_in_Cons>;
  List<List<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<List<uint64_t>>::cons(
            List<uint64_t>::cons(x, List<uint64_t>::nil()),
            List<List<uint64_t>>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        const List<uint64_t> &a1_value = *a1;
        uint64_t k = a0 + x;
        auto map_k = [=](List<List<uint64_t>> lsts) -> List<List<uint64_t>> {
          // Explicit stack replaces the non-tail recursion of map_k: _call
          // frames are pending calls, _after frames resume a caller.
          struct _call {
            List<List<uint64_t>> lsts;
          };

          struct _after_map_k_in_Cons {
            List<uint64_t> a00;
          };

          using _frame = std::variant<_call, _after_map_k_in_Cons>;
          List<List<uint64_t>> _result{};
          crane::small_vector<_frame> _stack;
          _stack.emplace_back(_call{std::move(lsts)});
          while (!_stack.empty()) {
            _frame &_popped = _stack.back();
            if (std::holds_alternative<_call>(_popped)) {
              auto _f = std::move(std::get<_call>(_popped));
              _stack.pop_back();
              List<List<uint64_t>> lsts = std::move(_f.lsts);
              if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                      lsts.v_mut())) {
                _result = List<List<uint64_t>>::nil();
              } else {
                auto &[a00, a10] =
                    std::get<typename List<List<uint64_t>>::Cons>(lsts.v_mut());
                _stack.emplace_back(_after_map_k_in_Cons{std::move(a00)});
                _stack.emplace_back(_call{*a10});
              }
            } else {
              auto _f = std::move(std::get<_after_map_k_in_Cons>(_popped));
              _stack.pop_back();
              List<uint64_t> a00 = std::move(_f.a00);
              _result = List<List<uint64_t>>::cons(
                  List<uint64_t>::cons(k, std::move(a00)), std::move(_result));
            }
          }
          return _result;
        };
        _stack.emplace_back(_after_insert_shift_in_Cons{l, k,
                                                        std::move(map_k)});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_insert_shift_in_Cons>(_popped));
      _stack.pop_back();
      List<uint64_t> l = std::move(_f.l);
      uint64_t k = _f.k;
      crane::fn<List<List<uint64_t>>(List<List<uint64_t>>)> map_k =
          std::move(_f.map_k);
      _result = List<List<uint64_t>>::cons(
          List<uint64_t>::cons(k, List<uint64_t>::cons(x, std::move(l))),
          map_k(std::move(_result)));
    }
  }
  return _result;
}

uint64_t InplaceFixSavedInFrame::sum_heads(const List<List<uint64_t>> &ls) {
  return ls.template fold_left<uint64_t>(
      [](uint64_t acc, const List<uint64_t> &l) -> uint64_t {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          return acc;
        } else {
          const auto &[a0, _] = std::get<typename List<uint64_t>::Cons>(l.v());
          return acc + a0;
        }
      },
      UINT64_C(0));
}
