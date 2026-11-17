#include "loopify_default.h"

List<uint64_t> LoopifyDefault::merge_steps(uint64_t n, const List<uint64_t> &xs,
                                           const List<uint64_t> &ys) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  const List<uint64_t> *_loop_ys = &ys;
  const List<uint64_t> *_loop_xs = &xs;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_xs->v())) {
        auto _value = *_loop_ys;
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        auto _value = *_loop_xs;
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      }
    } else {
      uint64_t n_ = _loop_n - 1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_xs->v())) {
        auto _value = *_loop_ys;
        (_write ? *(*_write =
                        std::make_shared<List<uint64_t>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_xs->v());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_ys->v())) {
          auto _value = *_loop_xs;
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_value)))
                  : _root.emplace(std::move(_value)));
          break;
        } else {
          const auto &[a01, a11] =
              std::get<typename List<uint64_t>::Cons>(_loop_ys->v());
          switch (Nat::compare(a00, a01)) {
          case Comparison::GT: {
            auto _cell = typename List<uint64_t>::Cons(a01, nullptr);
            List<uint64_t> &_node =
                (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                                std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
            _loop_ys = crane_raw(a11);
            _loop_xs = &*_loop_xs;
            _loop_n = n_;
            continue;
            break;
          }
          default: {
            auto _cell = typename List<uint64_t>::Cons(a00, nullptr);
            List<uint64_t> &_node =
                (_write ? *(*_write = std::make_shared<List<uint64_t>>(
                                std::move(_cell)))
                        : _root.emplace(std::move(_cell)));
            _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
            _loop_ys = &*_loop_ys;
            _loop_xs = crane_raw(a10);
            _loop_n = n_;
            continue;
          }
          }
        }
      }
    }
  }
  return std::move(*_root);
}

uint64_t LoopifyDefault::sum(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of sum: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_sum_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sum_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_sum_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyDefault::len(const List<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of len: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<uint64_t> *l;
  };

  struct _after_len_in_Cons {};

  using _frame = std::variant<_call, _after_len_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_len_in_Cons{});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_len_in_Cons>(_popped));
      _stack.pop_back();
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

Comparison Nat::compare(uint64_t n, uint64_t m) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _loop_m = m;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      if (_loop_m <= 0) {
        return Comparison::EQ;
      } else {
        uint64_t _x = _loop_m - 1;
        return Comparison::LT;
      }
    } else {
      uint64_t n_ = _loop_n - 1;
      if (_loop_m <= 0) {
        return Comparison::GT;
      } else {
        uint64_t m_ = _loop_m - 1;
        _loop_m = m_;
        _loop_n = n_;
      }
    }
  }
}
