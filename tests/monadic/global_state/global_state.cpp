#include "global_state.h"

uint64_t GlobalStateTests::fib_fun(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of fib_fun: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_fib_fun_in_S {
    uint64_t m;
  };

  struct _after_fib_fun_in_S_2 {
    uint64_t _tmp2;
  };

  using _frame =
      std::variant<_call, _after_fib_fun_in_S, _after_fib_fun_in_S_2>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m0 = n - 1;
        if (m0 <= 0) {
          _result = UINT64_C(1);
        } else {
          uint64_t m = m0 - 1;
          _stack.emplace_back(_after_fib_fun_in_S{m});
          _stack.emplace_back(_call{m0});
        }
      }
    } else if (std::holds_alternative<_after_fib_fun_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_fib_fun_in_S>(_popped));
      _stack.pop_back();
      uint64_t m = _f.m;
      _stack.emplace_back(_after_fib_fun_in_S_2{_result});
      _stack.emplace_back(_call{m});
    } else {
      auto _f = std::move(std::get<_after_fib_fun_in_S_2>(_popped));
      _stack.pop_back();
      _result = (_f._tmp2 + _result);
    }
  }
  return _result;
}

std::shared_ptr<uint64_t> GlobalStateTests::counter() {
  return std::make_shared<uint64_t>(UINT64_C(0));
}

uint64_t
GlobalStateTests::counter_next_mine(const std::shared_ptr<uint64_t> &ctr) {
  uint64_t a = *ctr;
  *ctr = (a + UINT64_C(1));
  return a;
}

std::string GlobalStateTests::gensym(const std::shared_ptr<uint64_t> &counter0,
                                     const std::string &prefix) {
  uint64_t v = counter_next_mine(counter0);
  return (prefix + std::to_string(v)).substr(0, 16777211);
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  while (true) {
    if (len <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t len0 = len - 1;
      auto _cell = typename List<uint64_t>::Cons(start, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      len = len0;
      start = (start + 1);
      continue;
    }
  }
  return std::move(*_root);
}
