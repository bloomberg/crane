#include "frame_box_pointer_scope.h"

uint64_t FrameBoxPointerScope::z4(const List<Sum<bool, uint64_t>> &l,
                                  const List<std::pair<uint64_t, bool>> &m) {
  // Explicit stack replaces the non-tail recursion of z4: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    List<std::pair<uint64_t, bool>> m;
    List<Sum<bool, uint64_t>> l;
  };

  struct _call_go {
    uint64_t _x1;
    List<uint64_t> k;
    crane::shared_box<List<Sum<bool, uint64_t>>> a1;
    crane::shared_box<List<std::pair<uint64_t, bool>>> a10;
  };

  using _frame = std::variant<_call, _call_go>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{m, l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (crane::holds_alternative<_call>(_popped)) {
      auto _f = std::move(crane::get<_call>(_popped));
      _stack.pop_back();
      const List<std::pair<uint64_t, bool>> &m = _f.m;
      const List<Sum<bool, uint64_t>> &l = _f.l;
      if (crane::holds_alternative<typename List<Sum<bool, uint64_t>>::Nil>(
              l.v())) {
        _result = UINT64_C(5);
      } else {
        const auto &[_, a1] =
            crane::get<typename List<Sum<bool, uint64_t>>::Cons>(l.v());
        if (crane::holds_alternative<
                typename List<std::pair<uint64_t, bool>>::Nil>(m.v())) {
          _result = UINT64_C(6);
        } else {
          const auto &[_, a10] =
              crane::get<typename List<std::pair<uint64_t, bool>>::Cons>(m.v());
          _stack.emplace_back(
              _call_go{UINT64_C(0), List<uint64_t>::nil(), a1, a10});
        }
      }
    } else {
      auto _f = std::move(crane::get<_call_go>(_popped));
      _stack.pop_back();
      uint64_t _x1 = _f._x1;
      const List<uint64_t> &k = _f.k;
      crane::shared_box<List<Sum<bool, uint64_t>>> a1 = std::move(_f.a1);
      crane::shared_box<List<std::pair<uint64_t, bool>>> a10 =
          std::move(_f.a10);
      if (crane::holds_alternative<typename List<uint64_t>::Nil>(k.v())) {
        _stack.emplace_back(_call{*a10, *a1});
      } else {
        const auto &[_, a11] = crane::get<typename List<uint64_t>::Cons>(k.v());
        _stack.emplace_back(
            _call_go{UINT64_C(0), *a11, std::move(a1), std::move(a10)});
      }
    }
  }
  return _result;
}
