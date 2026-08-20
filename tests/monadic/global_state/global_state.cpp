#include "global_state.h"

uint64_t
GlobalStateTests::fib_fun(uint64_t n) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _After_m: saves [m0], dispatches next recursive call.
  struct _After_m {
    uint64_t m0;
  };

  /// _Combine_m: receives partial results, combines with _result from final
  /// call.
  struct _Combine_m {
    uint64_t _result;
  };

  using _Frame = std::variant<_Enter, _After_m, _Combine_m>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified fib_fun: _Enter -> _After_m -> _Combine_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m0 = n - 1;
        if (m0 <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t m = m0 - 1;
          _stack.emplace_back(_After_m{m0});
          _stack.emplace_back(_Enter{m});
        }
      }
    } else if (std::holds_alternative<_After_m>(_frame)) {
      auto _f = std::move(std::get<_After_m>(_frame));
      _stack.emplace_back(_Combine_m{std::move(_result)});
      _stack.emplace_back(_Enter{_f.m0});
    } else {
      auto _f = std::move(std::get<_Combine_m>(_frame));
      _result = (std::move(_result) + std::move(_f._result));
    }
  }
  return _result;
}

uint64_t GlobalStateTests::counter() {
  return (_crane_globals[GlobalStateExamples::template ctr_idx<
              GlobalStateTests::nat_idx, uint64_t>()] = UINT64_C(0),
          GlobalStateExamples::template ctr_idx<GlobalStateTests::nat_idx,
                                                uint64_t>());
}

uint64_t GlobalStateTests::counter_next_mine(uint64_t ctr) {
  uint64_t a = std::any_cast<uint64_t>(_crane_globals.at(ctr));
  _crane_globals[ctr] = (a + UINT64_C(1));
  return a;
}

std::string GlobalStateTests::gensym(uint64_t counter0, std::string prefix) {
  uint64_t v = counter_next_mine(counter0);
  return prefix + std::to_string(v);
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_len = std::move(len);
  uint64_t _loop_start = std::move(start);
  while (true) {
    if (_loop_len <= 0) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t len0 = _loop_len - 1;
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(_loop_start, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_len = len0;
      _loop_start = (_loop_start + 1);
      continue;
    }
  }
  return std::move(*_head);
}
