#include "gb_maps.h"

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

bool Nat::eq_dec(uint64_t n, uint64_t m) {
  // Explicit stack replaces the non-tail recursion of eq_dec: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t m;
    uint64_t n;
  };

  struct _after_eq_dec_in_S {};

  using _frame = std::variant<_call, _after_eq_dec_in_S>;
  bool _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{m, n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t m = _f.m;
      uint64_t n = _f.n;
      if (n <= 0) {
        if (m <= 0) {
          _result = true;
        } else {
          uint64_t _x = m - 1;
          _result = false;
        }
      } else {
        uint64_t n0 = n - 1;
        if (m <= 0) {
          _result = false;
        } else {
          uint64_t n1 = m - 1;
          _stack.emplace_back(_after_eq_dec_in_S{});
          _stack.emplace_back(_call{n1, n0});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_eq_dec_in_S>(_popped));
      _stack.pop_back();
      bool s = std::move(_result);
      if (s) {
        _result = true;
      } else {
        _result = false;
      }
    }
  }
  return _result;
}

Positive Pos::succ(const Positive &x) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<Positive> _root{};
  std::shared_ptr<Positive> *_write = nullptr;
  const Positive *_loop_x = &x;
  while (true) {
    if (std::holds_alternative<typename Positive::XI>(_loop_x->v())) {
      const auto &[a0] = std::get<typename Positive::XI>(_loop_x->v());
      auto _cell = typename Positive::XO(nullptr);
      Positive &_node =
          (_write ? *(*_write = std::make_shared<Positive>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename Positive::XO>(_node.v_mut()).a0;
      _loop_x = crane_raw(a0);
      continue;
    } else if (std::holds_alternative<typename Positive::XO>(_loop_x->v())) {
      const auto &[a0] = std::get<typename Positive::XO>(_loop_x->v());
      auto _value = Positive::xi(*a0);
      (_write ? *(*_write = std::make_shared<Positive>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      auto _value = Positive::xo(Positive::xh());
      (_write ? *(*_write = std::make_shared<Positive>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    }
  }
  return std::move(*_root);
}

Positive Pos::add(const Positive &x, const Positive &y) {
  // Explicit stack replaces the non-tail recursion of add: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const Positive *y;
    const Positive *x;
  };

  struct _call_add_carry_entry {
    const Positive *y0;
    const Positive *x0;
  };

  struct _after_add_carry_entry_in_XI {};

  struct _after_add_carry_entry_in_XI_2 {};

  struct _after_add_carry_entry_in_XI_3 {};

  struct _after_add_carry_entry_in_XO {};

  struct _after_add_in_XI {};

  struct _after_add_in_XO {};

  struct _after_add_in_XO_2 {};

  struct _after_add_in_XO_3 {};

  using _frame = std::variant<
      _call, _call_add_carry_entry, _after_add_carry_entry_in_XI,
      _after_add_carry_entry_in_XI_2, _after_add_carry_entry_in_XI_3,
      _after_add_carry_entry_in_XO, _after_add_in_XI, _after_add_in_XO,
      _after_add_in_XO_2, _after_add_in_XO_3>;
  Positive _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&y, &x});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const Positive &y = *_f.y;
      const Positive &x = *_f.x;
      if (std::holds_alternative<typename Positive::XI>(x.v())) {
        const auto &[a00] = std::get<typename Positive::XI>(x.v());
        if (std::holds_alternative<typename Positive::XI>(y.v())) {
          const auto &[a01] = std::get<typename Positive::XI>(y.v());
          _stack.emplace_back(_after_add_carry_entry_in_XI{});
          _stack.emplace_back(
              _call_add_carry_entry{crane_raw(a01), crane_raw(a00)});
        } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
          const auto &[a01] = std::get<typename Positive::XO>(y.v());
          _stack.emplace_back(_after_add_in_XO{});
          _stack.emplace_back(_call{crane_raw(a01), crane_raw(a00)});
        } else {
          _result = Positive::xo(succ(*a00));
        }
      } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
        const auto &[a00] = std::get<typename Positive::XO>(x.v());
        if (std::holds_alternative<typename Positive::XI>(y.v())) {
          const auto &[a01] = std::get<typename Positive::XI>(y.v());
          _stack.emplace_back(_after_add_in_XI{});
          _stack.emplace_back(_call{crane_raw(a01), crane_raw(a00)});
        } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
          const auto &[a01] = std::get<typename Positive::XO>(y.v());
          _stack.emplace_back(_after_add_in_XO_2{});
          _stack.emplace_back(_call{crane_raw(a01), crane_raw(a00)});
        } else {
          _result = Positive::xi(*a00);
        }
      } else {
        if (std::holds_alternative<typename Positive::XI>(y.v())) {
          const auto &[a01] = std::get<typename Positive::XI>(y.v());
          _result = Positive::xo(succ(*a01));
        } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
          const auto &[a01] = std::get<typename Positive::XO>(y.v());
          _result = Positive::xi(*a01);
        } else {
          _result = Positive::xo(Positive::xh());
        }
      }
    } else if (std::holds_alternative<_call_add_carry_entry>(_popped)) {
      auto _f = std::move(std::get<_call_add_carry_entry>(_popped));
      _stack.pop_back();
      const Positive &y0 = *_f.y0;
      const Positive &x0 = *_f.x0;
      if (std::holds_alternative<typename Positive::XI>(x0.v())) {
        const auto &[a0] = std::get<typename Positive::XI>(x0.v());
        if (std::holds_alternative<typename Positive::XI>(y0.v())) {
          const auto &[a00] = std::get<typename Positive::XI>(y0.v());
          _stack.emplace_back(_after_add_carry_entry_in_XI_2{});
          _stack.emplace_back(
              _call_add_carry_entry{crane_raw(a00), crane_raw(a0)});
        } else if (std::holds_alternative<typename Positive::XO>(y0.v())) {
          const auto &[a00] = std::get<typename Positive::XO>(y0.v());
          _stack.emplace_back(_after_add_carry_entry_in_XO{});
          _stack.emplace_back(
              _call_add_carry_entry{crane_raw(a00), crane_raw(a0)});
        } else {
          _result = Positive::xi(succ(*a0));
        }
      } else if (std::holds_alternative<typename Positive::XO>(x0.v())) {
        const auto &[a0] = std::get<typename Positive::XO>(x0.v());
        if (std::holds_alternative<typename Positive::XI>(y0.v())) {
          const auto &[a00] = std::get<typename Positive::XI>(y0.v());
          _stack.emplace_back(_after_add_carry_entry_in_XI_3{});
          _stack.emplace_back(
              _call_add_carry_entry{crane_raw(a00), crane_raw(a0)});
        } else if (std::holds_alternative<typename Positive::XO>(y0.v())) {
          const auto &[a00] = std::get<typename Positive::XO>(y0.v());
          _stack.emplace_back(_after_add_in_XO_3{});
          _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
        } else {
          _result = Positive::xo(succ(*a0));
        }
      } else {
        if (std::holds_alternative<typename Positive::XI>(y0.v())) {
          const auto &[a00] = std::get<typename Positive::XI>(y0.v());
          _result = Positive::xi(succ(*a00));
        } else if (std::holds_alternative<typename Positive::XO>(y0.v())) {
          const auto &[a00] = std::get<typename Positive::XO>(y0.v());
          _result = Positive::xo(succ(*a00));
        } else {
          _result = Positive::xi(Positive::xh());
        }
      }
    } else if (std::holds_alternative<_after_add_carry_entry_in_XI>(_popped)) {
      auto _f = std::move(std::get<_after_add_carry_entry_in_XI>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    } else if (std::holds_alternative<_after_add_carry_entry_in_XI_2>(_popped)) {
      auto _f = std::move(std::get<_after_add_carry_entry_in_XI_2>(_popped));
      _stack.pop_back();
      _result = Positive::xi(std::move(_result));
    } else if (std::holds_alternative<_after_add_carry_entry_in_XI_3>(_popped)) {
      auto _f = std::move(std::get<_after_add_carry_entry_in_XI_3>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    } else if (std::holds_alternative<_after_add_carry_entry_in_XO>(_popped)) {
      auto _f = std::move(std::get<_after_add_carry_entry_in_XO>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    } else if (std::holds_alternative<_after_add_in_XI>(_popped)) {
      auto _f = std::move(std::get<_after_add_in_XI>(_popped));
      _stack.pop_back();
      _result = Positive::xi(std::move(_result));
    } else if (std::holds_alternative<_after_add_in_XO>(_popped)) {
      auto _f = std::move(std::get<_after_add_in_XO>(_popped));
      _stack.pop_back();
      _result = Positive::xi(std::move(_result));
    } else if (std::holds_alternative<_after_add_in_XO_2>(_popped)) {
      auto _f = std::move(std::get<_after_add_in_XO_2>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_add_in_XO_3>(_popped));
      _stack.pop_back();
      _result = Positive::xi(std::move(_result));
    }
  }
  return _result;
}

Positive Pos::add_carry(const Positive &x, const Positive &y) {
  // Explicit stack replaces the non-tail recursion of add_carry: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const Positive *y;
    const Positive *x;
  };

  struct _call_add_entry {
    const Positive *y0;
    const Positive *x0;
  };

  struct _after_add_carry_in_XI {};

  struct _after_add_carry_in_XI_2 {};

  struct _after_add_carry_in_XI_3 {};

  struct _after_add_carry_in_XO {};

  struct _after_add_entry_in_XI {};

  struct _after_add_entry_in_XO {};

  struct _after_add_entry_in_XO_2 {};

  struct _after_add_entry_in_XO_3 {};

  using _frame = std::variant<
      _call, _call_add_entry, _after_add_carry_in_XI, _after_add_carry_in_XI_2,
      _after_add_carry_in_XI_3, _after_add_carry_in_XO, _after_add_entry_in_XI,
      _after_add_entry_in_XO, _after_add_entry_in_XO_2,
      _after_add_entry_in_XO_3>;
  Positive _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&y, &x});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const Positive &y = *_f.y;
      const Positive &x = *_f.x;
      if (std::holds_alternative<typename Positive::XI>(x.v())) {
        const auto &[a00] = std::get<typename Positive::XI>(x.v());
        if (std::holds_alternative<typename Positive::XI>(y.v())) {
          const auto &[a01] = std::get<typename Positive::XI>(y.v());
          _stack.emplace_back(_after_add_carry_in_XI{});
          _stack.emplace_back(_call{crane_raw(a01), crane_raw(a00)});
        } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
          const auto &[a01] = std::get<typename Positive::XO>(y.v());
          _stack.emplace_back(_after_add_carry_in_XO{});
          _stack.emplace_back(_call{crane_raw(a01), crane_raw(a00)});
        } else {
          _result = Positive::xi(succ(*a00));
        }
      } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
        const auto &[a00] = std::get<typename Positive::XO>(x.v());
        if (std::holds_alternative<typename Positive::XI>(y.v())) {
          const auto &[a01] = std::get<typename Positive::XI>(y.v());
          _stack.emplace_back(_after_add_carry_in_XI_2{});
          _stack.emplace_back(_call{crane_raw(a01), crane_raw(a00)});
        } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
          const auto &[a01] = std::get<typename Positive::XO>(y.v());
          _stack.emplace_back(_after_add_entry_in_XO{});
          _stack.emplace_back(_call_add_entry{crane_raw(a01), crane_raw(a00)});
        } else {
          _result = Positive::xo(succ(*a00));
        }
      } else {
        if (std::holds_alternative<typename Positive::XI>(y.v())) {
          const auto &[a01] = std::get<typename Positive::XI>(y.v());
          _result = Positive::xi(succ(*a01));
        } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
          const auto &[a01] = std::get<typename Positive::XO>(y.v());
          _result = Positive::xo(succ(*a01));
        } else {
          _result = Positive::xi(Positive::xh());
        }
      }
    } else if (std::holds_alternative<_call_add_entry>(_popped)) {
      auto _f = std::move(std::get<_call_add_entry>(_popped));
      _stack.pop_back();
      const Positive &y0 = *_f.y0;
      const Positive &x0 = *_f.x0;
      if (std::holds_alternative<typename Positive::XI>(x0.v())) {
        const auto &[a0] = std::get<typename Positive::XI>(x0.v());
        if (std::holds_alternative<typename Positive::XI>(y0.v())) {
          const auto &[a00] = std::get<typename Positive::XI>(y0.v());
          _stack.emplace_back(_after_add_carry_in_XI_3{});
          _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
        } else if (std::holds_alternative<typename Positive::XO>(y0.v())) {
          const auto &[a00] = std::get<typename Positive::XO>(y0.v());
          _stack.emplace_back(_after_add_entry_in_XO_2{});
          _stack.emplace_back(_call_add_entry{crane_raw(a00), crane_raw(a0)});
        } else {
          _result = Positive::xo(succ(*a0));
        }
      } else if (std::holds_alternative<typename Positive::XO>(x0.v())) {
        const auto &[a0] = std::get<typename Positive::XO>(x0.v());
        if (std::holds_alternative<typename Positive::XI>(y0.v())) {
          const auto &[a00] = std::get<typename Positive::XI>(y0.v());
          _stack.emplace_back(_after_add_entry_in_XI{});
          _stack.emplace_back(_call_add_entry{crane_raw(a00), crane_raw(a0)});
        } else if (std::holds_alternative<typename Positive::XO>(y0.v())) {
          const auto &[a00] = std::get<typename Positive::XO>(y0.v());
          _stack.emplace_back(_after_add_entry_in_XO_3{});
          _stack.emplace_back(_call_add_entry{crane_raw(a00), crane_raw(a0)});
        } else {
          _result = Positive::xi(*a0);
        }
      } else {
        if (std::holds_alternative<typename Positive::XI>(y0.v())) {
          const auto &[a00] = std::get<typename Positive::XI>(y0.v());
          _result = Positive::xo(succ(*a00));
        } else if (std::holds_alternative<typename Positive::XO>(y0.v())) {
          const auto &[a00] = std::get<typename Positive::XO>(y0.v());
          _result = Positive::xi(*a00);
        } else {
          _result = Positive::xo(Positive::xh());
        }
      }
    } else if (std::holds_alternative<_after_add_carry_in_XI>(_popped)) {
      auto _f = std::move(std::get<_after_add_carry_in_XI>(_popped));
      _stack.pop_back();
      _result = Positive::xi(std::move(_result));
    } else if (std::holds_alternative<_after_add_carry_in_XI_2>(_popped)) {
      auto _f = std::move(std::get<_after_add_carry_in_XI_2>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    } else if (std::holds_alternative<_after_add_carry_in_XI_3>(_popped)) {
      auto _f = std::move(std::get<_after_add_carry_in_XI_3>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    } else if (std::holds_alternative<_after_add_carry_in_XO>(_popped)) {
      auto _f = std::move(std::get<_after_add_carry_in_XO>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    } else if (std::holds_alternative<_after_add_entry_in_XI>(_popped)) {
      auto _f = std::move(std::get<_after_add_entry_in_XI>(_popped));
      _stack.pop_back();
      _result = Positive::xi(std::move(_result));
    } else if (std::holds_alternative<_after_add_entry_in_XO>(_popped)) {
      auto _f = std::move(std::get<_after_add_entry_in_XO>(_popped));
      _stack.pop_back();
      _result = Positive::xi(std::move(_result));
    } else if (std::holds_alternative<_after_add_entry_in_XO_2>(_popped)) {
      auto _f = std::move(std::get<_after_add_entry_in_XO_2>(_popped));
      _stack.pop_back();
      _result = Positive::xi(std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_add_entry_in_XO_3>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    }
  }
  return _result;
}

Positive Pos::pred_double(const Positive &x) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<Positive> _root{};
  std::shared_ptr<Positive> *_write = nullptr;
  const Positive *_loop_x = &x;
  while (true) {
    if (std::holds_alternative<typename Positive::XI>(_loop_x->v())) {
      const auto &[a0] = std::get<typename Positive::XI>(_loop_x->v());
      auto _value = Positive::xi(Positive::xo(*a0));
      (_write ? *(*_write = std::make_shared<Positive>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else if (std::holds_alternative<typename Positive::XO>(_loop_x->v())) {
      const auto &[a0] = std::get<typename Positive::XO>(_loop_x->v());
      auto _cell = typename Positive::XI(nullptr);
      Positive &_node =
          (_write ? *(*_write = std::make_shared<Positive>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename Positive::XI>(_node.v_mut()).a0;
      _loop_x = crane_raw(a0);
      continue;
    } else {
      auto _value = Positive::xh();
      (_write ? *(*_write = std::make_shared<Positive>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    }
  }
  return std::move(*_root);
}

Positive Pos::mul(const Positive &x, Positive y) {
  // Explicit stack replaces the non-tail recursion of mul: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const Positive *x;
  };

  struct _after_mul_in_XI {};

  struct _after_mul_in_XO {};

  using _frame = std::variant<_call, _after_mul_in_XI, _after_mul_in_XO>;
  Positive _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&x});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const Positive &x = *_f.x;
      if (std::holds_alternative<typename Positive::XI>(x.v())) {
        const auto &[a0] = std::get<typename Positive::XI>(x.v());
        _stack.emplace_back(_after_mul_in_XI{});
        _stack.emplace_back(_call{crane_raw(a0)});
      } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
        const auto &[a0] = std::get<typename Positive::XO>(x.v());
        _stack.emplace_back(_after_mul_in_XO{});
        _stack.emplace_back(_call{crane_raw(a0)});
      } else {
        _result = y;
      }
    } else if (std::holds_alternative<_after_mul_in_XI>(_popped)) {
      auto _f = std::move(std::get<_after_mul_in_XI>(_popped));
      _stack.pop_back();
      _result = add(y, Positive::xo(std::move(_result)));
    } else {
      auto _f = std::move(std::get<_after_mul_in_XO>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    }
  }
  return _result;
}

Comparison Pos::compare_cont(Comparison r, const Positive &x,
                             const Positive &y) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const Positive *_loop_y = &y;
  const Positive *_loop_x = &x;
  Comparison _loop_r = r;
  while (true) {
    if (std::holds_alternative<typename Positive::XI>(_loop_x->v())) {
      const auto &[a0] = std::get<typename Positive::XI>(_loop_x->v());
      if (std::holds_alternative<typename Positive::XI>(_loop_y->v())) {
        const auto &[a00] = std::get<typename Positive::XI>(_loop_y->v());
        _loop_y = crane_raw(a00);
        _loop_x = crane_raw(a0);
      } else if (std::holds_alternative<typename Positive::XO>(_loop_y->v())) {
        const auto &[a00] = std::get<typename Positive::XO>(_loop_y->v());
        _loop_y = crane_raw(a00);
        _loop_x = crane_raw(a0);
        _loop_r = Comparison::GT;
      } else {
        return Comparison::GT;
      }
    } else if (std::holds_alternative<typename Positive::XO>(_loop_x->v())) {
      const auto &[a0] = std::get<typename Positive::XO>(_loop_x->v());
      if (std::holds_alternative<typename Positive::XI>(_loop_y->v())) {
        const auto &[a00] = std::get<typename Positive::XI>(_loop_y->v());
        _loop_y = crane_raw(a00);
        _loop_x = crane_raw(a0);
        _loop_r = Comparison::LT;
      } else if (std::holds_alternative<typename Positive::XO>(_loop_y->v())) {
        const auto &[a00] = std::get<typename Positive::XO>(_loop_y->v());
        _loop_y = crane_raw(a00);
        _loop_x = crane_raw(a0);
      } else {
        return Comparison::GT;
      }
    } else {
      if (std::holds_alternative<typename Positive::XH>(_loop_y->v())) {
        return _loop_r;
      } else {
        return Comparison::LT;
      }
    }
  }
}

Comparison Pos::compare(const Positive &x0_, const Positive &x1_) {
  return compare_cont(Comparison::EQ, x0_, x1_);
}

bool Pos::eqb(const Positive &p, const Positive &q) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const Positive *_loop_q = &q;
  const Positive *_loop_p = &p;
  while (true) {
    if (std::holds_alternative<typename Positive::XI>(_loop_p->v())) {
      const auto &[a0] = std::get<typename Positive::XI>(_loop_p->v());
      if (std::holds_alternative<typename Positive::XI>(_loop_q->v())) {
        const auto &[a00] = std::get<typename Positive::XI>(_loop_q->v());
        _loop_q = crane_raw(a00);
        _loop_p = crane_raw(a0);
      } else {
        return false;
      }
    } else if (std::holds_alternative<typename Positive::XO>(_loop_p->v())) {
      const auto &[a0] = std::get<typename Positive::XO>(_loop_p->v());
      if (std::holds_alternative<typename Positive::XO>(_loop_q->v())) {
        const auto &[a00] = std::get<typename Positive::XO>(_loop_q->v());
        _loop_q = crane_raw(a00);
        _loop_p = crane_raw(a0);
      } else {
        return false;
      }
    } else {
      if (std::holds_alternative<typename Positive::XH>(_loop_q->v())) {
        return true;
      } else {
        return false;
      }
    }
  }
}

bool Coq_Pos::eq_dec(const Positive &p, const Positive &x0) {
  // Explicit stack replaces the non-tail recursion of eq_dec: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const Positive *x0;
    const Positive *p;
  };

  struct _after_eq_dec_in_XI {};

  struct _after_eq_dec_in_XO {};

  using _frame = std::variant<_call, _after_eq_dec_in_XI, _after_eq_dec_in_XO>;
  bool _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&x0, &p});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const Positive &x0 = *_f.x0;
      const Positive &p = *_f.p;
      if (std::holds_alternative<typename Positive::XI>(p.v())) {
        const auto &[a0] = std::get<typename Positive::XI>(p.v());
        if (std::holds_alternative<typename Positive::XI>(x0.v())) {
          const auto &[a00] = std::get<typename Positive::XI>(x0.v());
          _stack.emplace_back(_after_eq_dec_in_XI{});
          _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
        } else {
          _result = false;
        }
      } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
        const auto &[a0] = std::get<typename Positive::XO>(p.v());
        if (std::holds_alternative<typename Positive::XO>(x0.v())) {
          const auto &[a00] = std::get<typename Positive::XO>(x0.v());
          _stack.emplace_back(_after_eq_dec_in_XO{});
          _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
        } else {
          _result = false;
        }
      } else {
        if (std::holds_alternative<typename Positive::XH>(x0.v())) {
          _result = true;
        } else {
          _result = false;
        }
      }
    } else if (std::holds_alternative<_after_eq_dec_in_XI>(_popped)) {
      auto _f = std::move(std::get<_after_eq_dec_in_XI>(_popped));
      _stack.pop_back();
      if (std::move(_result)) {
        _result = true;
      } else {
        _result = false;
      }
    } else {
      auto _f = std::move(std::get<_after_eq_dec_in_XO>(_popped));
      _stack.pop_back();
      if (std::move(_result)) {
        _result = true;
      } else {
        _result = false;
      }
    }
  }
  return _result;
}

Z BinInt::double_(const Z &x) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    return Z::zpos(Positive::xo(a0));
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    return Z::zneg(Positive::xo(a0));
  }
}

Z BinInt::succ_double(const Z &x) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::zpos(Positive::xh());
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    return Z::zpos(Positive::xi(a0));
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    return Z::zneg(Pos::pred_double(a0));
  }
}

Z BinInt::pred_double(const Z &x) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::zneg(Positive::xh());
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    return Z::zpos(Pos::pred_double(a0));
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    return Z::zneg(Positive::xi(a0));
  }
}

Z BinInt::pos_sub(const Positive &x, const Positive &y) {
  // Explicit stack replaces the non-tail recursion of pos_sub: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const Positive *y;
    const Positive *x;
  };

  struct _after_pos_sub_in_XI {};

  struct _after_pos_sub_in_XI_2 {};

  struct _after_pos_sub_in_XO {};

  struct _after_pos_sub_in_XO_2 {};

  using _frame =
      std::variant<_call, _after_pos_sub_in_XI, _after_pos_sub_in_XI_2,
                   _after_pos_sub_in_XO, _after_pos_sub_in_XO_2>;
  Z _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&y, &x});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const Positive &y = *_f.y;
      const Positive &x = *_f.x;
      if (std::holds_alternative<typename Positive::XI>(x.v())) {
        const auto &[a0] = std::get<typename Positive::XI>(x.v());
        if (std::holds_alternative<typename Positive::XI>(y.v())) {
          const auto &[a00] = std::get<typename Positive::XI>(y.v());
          _stack.emplace_back(_after_pos_sub_in_XI{});
          _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
        } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
          const auto &[a00] = std::get<typename Positive::XO>(y.v());
          _stack.emplace_back(_after_pos_sub_in_XO{});
          _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
        } else {
          _result = Z::zpos(Positive::xo(*a0));
        }
      } else if (std::holds_alternative<typename Positive::XO>(x.v())) {
        const auto &[a0] = std::get<typename Positive::XO>(x.v());
        if (std::holds_alternative<typename Positive::XI>(y.v())) {
          const auto &[a00] = std::get<typename Positive::XI>(y.v());
          _stack.emplace_back(_after_pos_sub_in_XI_2{});
          _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
        } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
          const auto &[a00] = std::get<typename Positive::XO>(y.v());
          _stack.emplace_back(_after_pos_sub_in_XO_2{});
          _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
        } else {
          _result = Z::zpos(Pos::pred_double(*a0));
        }
      } else {
        if (std::holds_alternative<typename Positive::XI>(y.v())) {
          const auto &[a00] = std::get<typename Positive::XI>(y.v());
          _result = Z::zneg(Positive::xo(*a00));
        } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
          const auto &[a00] = std::get<typename Positive::XO>(y.v());
          _result = Z::zneg(Pos::pred_double(*a00));
        } else {
          _result = Z::z0();
        }
      }
    } else if (std::holds_alternative<_after_pos_sub_in_XI>(_popped)) {
      auto _f = std::move(std::get<_after_pos_sub_in_XI>(_popped));
      _stack.pop_back();
      _result = BinInt::double_(std::move(_result));
    } else if (std::holds_alternative<_after_pos_sub_in_XI_2>(_popped)) {
      auto _f = std::move(std::get<_after_pos_sub_in_XI_2>(_popped));
      _stack.pop_back();
      _result = BinInt::pred_double(std::move(_result));
    } else if (std::holds_alternative<_after_pos_sub_in_XO>(_popped)) {
      auto _f = std::move(std::get<_after_pos_sub_in_XO>(_popped));
      _stack.pop_back();
      _result = BinInt::succ_double(std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_pos_sub_in_XO_2>(_popped));
      _stack.pop_back();
      _result = BinInt::double_(std::move(_result));
    }
  }
  return _result;
}

Z BinInt::add(const Z &x, const Z &y) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return y;
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return x;
    } else if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zpos>(y.v());
      return Z::zpos(Pos::add(a0, a00));
    } else {
      const auto &[a00] = std::get<typename Z::Zneg>(y.v());
      return BinInt::pos_sub(a0, a00);
    }
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return x;
    } else if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zpos>(y.v());
      return BinInt::pos_sub(a00, a0);
    } else {
      const auto &[a00] = std::get<typename Z::Zneg>(y.v());
      return Z::zneg(Pos::add(a0, a00));
    }
  }
}

Z BinInt::opp(const Z &x) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    return Z::zneg(a0);
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    return Z::zpos(a0);
  }
}

Z BinInt::sub(const Z &m, const Z &n) { return BinInt::add(m, BinInt::opp(n)); }

Z BinInt::mul(const Z &x, const Z &y) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    return Z::z0();
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return Z::z0();
    } else if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zpos>(y.v());
      return Z::zpos(Pos::mul(a0, a00));
    } else {
      const auto &[a00] = std::get<typename Z::Zneg>(y.v());
      return Z::zneg(Pos::mul(a0, a00));
    }
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return Z::z0();
    } else if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zpos>(y.v());
      return Z::zneg(Pos::mul(a0, a00));
    } else {
      const auto &[a00] = std::get<typename Z::Zneg>(y.v());
      return Z::zpos(Pos::mul(a0, a00));
    }
  }
}

Comparison BinInt::compare(const Z &x, const Z &y) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return Comparison::EQ;
    } else if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      return Comparison::LT;
    } else {
      return Comparison::GT;
    }
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zpos>(y.v());
      return Pos::compare(a0, a00);
    } else {
      return Comparison::GT;
    }
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    if (std::holds_alternative<typename Z::Zneg>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zneg>(y.v());
      return Datatypes::CompOpp(Pos::compare(a0, a00));
    } else {
      return Comparison::LT;
    }
  }
}

bool BinInt::leb(const Z &x, const Z &y) {
  switch (BinInt::compare(x, y)) {
  case Comparison::GT: {
    return false;
  }
  default: {
    return true;
  }
  }
}

bool BinInt::ltb(const Z &x, const Z &y) {
  switch (BinInt::compare(x, y)) {
  case Comparison::LT: {
    return true;
  }
  default: {
    return false;
  }
  }
}

bool BinInt::eqb(const Z &x, const Z &y) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return true;
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zpos>(y.v());
      return Pos::eqb(a0, a00);
    } else {
      return false;
    }
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    if (std::holds_alternative<typename Z::Zneg>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zneg>(y.v());
      return Pos::eqb(a0, a00);
    } else {
      return false;
    }
  }
}

Z BinInt::max(Z n, Z m) {
  switch (BinInt::compare(n, m)) {
  case Comparison::LT: {
    return m;
  }
  default: {
    return n;
  }
  }
}

bool BinInt::eq_dec(const Z &x, const Z &y) {
  if (std::holds_alternative<typename Z::Z0>(x.v())) {
    if (std::holds_alternative<typename Z::Z0>(y.v())) {
      return true;
    } else {
      return false;
    }
  } else if (std::holds_alternative<typename Z::Zpos>(x.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(x.v());
    if (std::holds_alternative<typename Z::Zpos>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zpos>(y.v());
      if (Coq_Pos::eq_dec(a0, a00)) {
        return true;
      } else {
        return false;
      }
    } else {
      return false;
    }
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(x.v());
    if (std::holds_alternative<typename Z::Zneg>(y.v())) {
      const auto &[a00] = std::get<typename Z::Zneg>(y.v());
      if (Coq_Pos::eq_dec(a0, a00)) {
        return true;
      } else {
        return false;
      }
    } else {
      return false;
    }
  }
}

Compare<uint64_t> Nat_as_OT::compare(uint64_t x, uint64_t y) {
  switch (Nat::compare(x, y)) {
  case Comparison::EQ: {
    return Compare<uint64_t>::eq();
  }
  case Comparison::LT: {
    return Compare<uint64_t>::lt();
  }
  case Comparison::GT: {
    return Compare<uint64_t>::gt();
  }
  default:
    std::unreachable();
  }
}

bool Nat_as_OT::eq_dec(uint64_t x0_, uint64_t x1_) {
  return Nat::eq_dec(x0_, x1_);
}

Z Z_as_Int::add(const Z &x0_, const Z &x1_) { return BinInt::add(x0_, x1_); }

Z Z_as_Int::opp(const Z &x0_) { return BinInt::opp(x0_); }

Z Z_as_Int::sub(const Z &x0_, const Z &x1_) { return BinInt::sub(x0_, x1_); }

Z Z_as_Int::mul(const Z &x0_, const Z &x1_) { return BinInt::mul(x0_, x1_); }

Z Z_as_Int::max(Z x0_, Z x1_) {
  return BinInt::max(std::move(x0_), std::move(x1_));
}

bool Z_as_Int::eqb(const Z &x0_, const Z &x1_) { return BinInt::eqb(x0_, x1_); }

bool Z_as_Int::ltb(const Z &x0_, const Z &x1_) { return BinInt::ltb(x0_, x1_); }

bool Z_as_Int::leb(const Z &x0_, const Z &x1_) { return BinInt::leb(x0_, x1_); }

bool Z_as_Int::eq_dec(const Z &x0_, const Z &x1_) {
  return BinInt::eq_dec(x0_, x1_);
}

bool Z_as_Int::gt_le_dec(const Z &i, const Z &j) {
  bool b = BinInt::ltb(j, i);
  if (b) {
    return true;
  } else {
    return false;
  }
}

bool Z_as_Int::ge_lt_dec(const Z &i, const Z &j) {
  bool b = BinInt::ltb(i, j);
  if (b) {
    return false;
  } else {
    return true;
  }
}

Z Z_as_Int::i2z(Z n) { return n; }

uint64_t GbMaps::next(uint64_t s) {
  auto &&_once1 = ((s * UINT64_C(75)) + UINT64_C(74));
  auto &&_once2 = UINT64_C(65537);
  return (_once2 ? _once1 % _once2 : _once1);
}

List<uint64_t> GbMaps::randoms(uint64_t n, uint64_t s) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_s = s;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = typename List<uint64_t>::Cons(_loop_s, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_s = next(_loop_s);
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t GbMaps::maps(uint64_t n, uint64_t rounds) {
  return ListDef::seq(UINT64_C(0), rounds).template fold_left<uint64_t>(
      [=](uint64_t acc, uint64_t i) {
        GbMaps::M::template t<uint64_t> m =
            randoms(n, (i + UINT64_C(11))).template fold_left<
                                GbMaps::M::template t<uint64_t>>(
                                [=](const GbMaps::M::template t<uint64_t> &m0,
                                    uint64_t x) {
                                  auto &&_once1 = UINT64_C(4000);
                                  return M::template add<uint64_t>(
                                      (_once1 ? x % _once1 : x), (x + i), m0);
                                },
                                M::template empty<uint64_t>());
        GbMaps::M::template t<uint64_t> m0 =
            M::template map<uint64_t, uint64_t>(
                [](uint64_t v) {
                  auto &&_once2 = UINT64_C(1000);
                  return (_once2 ? v % _once2 : v);
                },
                std::move(m));
        return ((acc + M::template fold<uint64_t, uint64_t>(
                           [](uint64_t k, uint64_t v, uint64_t a) {
                             auto &&_once3 = (a + (k * v));
                             auto &&_once4 = UINT64_C(65535);
                             return (_once4 ? _once3 % _once4 : _once3);
                           },
                           m0,
                           UINT64_C(0))) +
                [&]() -> uint64_t {
                  auto _cs = M::template find<uint64_t>(UINT64_C(17), m0);
                  if (_cs.has_value()) {
                    const uint64_t &v = *_cs;
                    return v;
                  } else {
                    return UINT64_C(0);
                  }
                }());
      },
      UINT64_C(0));
}

Comparison Datatypes::CompOpp(Comparison r) {
  switch (r) {
  case Comparison::EQ: {
    return Comparison::EQ;
  }
  case Comparison::LT: {
    return Comparison::GT;
  }
  case Comparison::GT: {
    return Comparison::LT;
  }
  default:
    std::unreachable();
  }
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<uint64_t>> _root{};
  std::shared_ptr<List<uint64_t>> *_write = nullptr;
  uint64_t _loop_len = len;
  uint64_t _loop_start = start;
  while (true) {
    if (_loop_len <= 0) {
      auto _value = List<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<List<uint64_t>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t len0 = _loop_len - 1;
      auto _cell = typename List<uint64_t>::Cons(_loop_start, nullptr);
      List<uint64_t> &_node =
          (_write ? *(*_write =
                          std::make_shared<List<uint64_t>>(std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename List<uint64_t>::Cons>(_node.v_mut()).l;
      _loop_len = len0;
      _loop_start = (_loop_start + 1);
      continue;
    }
  }
  return std::move(*_root);
}
