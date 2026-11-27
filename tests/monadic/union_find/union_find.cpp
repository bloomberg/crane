#include "union_find.h"

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
      if (_result) {
        _result = true;
      } else {
        _result = false;
      }
    } else {
      auto _f = std::move(std::get<_after_eq_dec_in_XO>(_popped));
      _stack.pop_back();
      if (_result) {
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
      auto _value = Positive::xi(crane::shared_child(a0));
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
          _result = Positive::xi(crane::shared_child(a00));
        }
      } else {
        if (std::holds_alternative<typename Positive::XI>(y.v())) {
          const auto &[a01] = std::get<typename Positive::XI>(y.v());
          _result = Positive::xo(succ(*a01));
        } else if (std::holds_alternative<typename Positive::XO>(y.v())) {
          const auto &[a01] = std::get<typename Positive::XO>(y.v());
          _result = Positive::xi(crane::shared_child(a01));
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
          _result = Positive::xi(crane::shared_child(a0));
        }
      } else {
        if (std::holds_alternative<typename Positive::XI>(y0.v())) {
          const auto &[a00] = std::get<typename Positive::XI>(y0.v());
          _result = Positive::xo(succ(*a00));
        } else if (std::holds_alternative<typename Positive::XO>(y0.v())) {
          const auto &[a00] = std::get<typename Positive::XO>(y0.v());
          _result = Positive::xi(crane::shared_child(a00));
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
      auto _value = Positive::xi(Positive::xo(crane::shared_child(a0)));
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
        r = Comparison::GT;
      } else {
        return Comparison::GT;
      }
    } else if (std::holds_alternative<typename Positive::XO>(_loop_x->v())) {
      const auto &[a0] = std::get<typename Positive::XO>(_loop_x->v());
      if (std::holds_alternative<typename Positive::XI>(_loop_y->v())) {
        const auto &[a00] = std::get<typename Positive::XI>(_loop_y->v());
        _loop_y = crane_raw(a00);
        _loop_x = crane_raw(a0);
        r = Comparison::LT;
      } else if (std::holds_alternative<typename Positive::XO>(_loop_y->v())) {
        const auto &[a00] = std::get<typename Positive::XO>(_loop_y->v());
        _loop_y = crane_raw(a00);
        _loop_x = crane_raw(a0);
      } else {
        return Comparison::GT;
      }
    } else {
      if (std::holds_alternative<typename Positive::XH>(_loop_y->v())) {
        return r;
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
          _result = Z::zpos(Positive::xo(crane::shared_child(a0)));
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
          _result = Z::zneg(Positive::xo(crane::shared_child(a00)));
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
  switch ((x < y ? Comparison::LT
                 : (y < x ? Comparison::GT : Comparison::EQ))) {
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

bool Nat_as_OT::eq_dec(uint64_t x0_, uint64_t x1_) { return x0_ == x1_; }

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

void init_ST(STRefs, std::span<std::pair<uint64_t, uint64_t>> a, uint64_t n,
             uint64_t i) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (i < n) {
      a[i] = std::make_pair(i, UINT64_C(0));
      i = (i + 1);
    } else {
      return;
    }
  }
}

std::shared_ptr<crane::array_storage<node>> make_ST(STRefs r, uint64_t n) {
  std::shared_ptr<crane::array_storage<node>> a =
      std::make_shared<crane::array_storage<std::pair<uint64_t, uint64_t>>>(
          crane::st::extent(n), std::make_pair(UINT64_C(0), UINT64_C(0)));
  init_ST(r, std::span{*a}, n, UINT64_C(0));
  return a;
}

uint64_t find_ST(STRefs, std::span<std::pair<uint64_t, uint64_t>> a,
                 uint64_t fuel, uint64_t x) {
  // Explicit stack replaces the non-tail recursion of find_ST: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t x;
    uint64_t fuel;
  };

  struct _after_find_ST_in_false {
    uint64_t x;
    uint64_t k;
  };

  using _frame = std::variant<_call, _after_find_ST_in_false>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{x, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t x = _f.x;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = x;
      } else {
        uint64_t fuel_ = fuel - 1;
        auto [p, k] = a[x];
        if (p == x) {
          _result = x;
        } else {
          _stack.emplace_back(_after_find_ST_in_false{x, k});
          _stack.emplace_back(_call{p, fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_find_ST_in_false>(_popped));
      _stack.pop_back();
      uint64_t x = _f.x;
      uint64_t k = _f.k;
      a[x] = std::make_pair(_result, k);
    }
  }
  return _result;
}

void union_ST(STRefs r, uint64_t n, std::span<std::pair<uint64_t, uint64_t>> a,
              uint64_t x, uint64_t y) {
  uint64_t rx = find_ST(r, a, n, x);
  uint64_t ry = find_ST(r, a, n, y);
  if (rx == ry) {
    return;
  } else {
    auto [_, kx] = a[rx];
    auto [_, ky] = a[ry];
    if (kx < ky) {
      a[rx] = std::make_pair(ry, kx);
    } else if (ky < kx) {
      a[ry] = std::make_pair(rx, ky);
    } else {
      a[ry] = std::make_pair(rx, ky);
      a[rx] = std::make_pair(rx, (kx + 1));
    }
  }
}

bool same_ST(STRefs r, uint64_t n, std::span<std::pair<uint64_t, uint64_t>> a,
             uint64_t x, uint64_t y) {
  uint64_t rx = find_ST(r, a, n, x);
  uint64_t ry = find_ST(r, a, n, y);
  return rx == ry;
}

List<bool> run_ST(STRefs r, uint64_t n,
                  std::span<std::pair<uint64_t, uint64_t>> a,
                  const List<Op> &ops) {
  // Explicit stack replaces the non-tail recursion of run_ST: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const List<Op> *ops;
  };

  struct _after_run_ST_in_Same {
    bool b;
  };

  using _frame = std::variant<_call, _after_run_ST_in_Same>;
  List<bool> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&ops});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const List<Op> &ops = *_f.ops;
      if (std::holds_alternative<typename List<Op>::Nil>(ops.v())) {
        _result = List<bool>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<Op>::Cons>(ops.v());
        if (std::holds_alternative<typename Op::Union>(a0.v())) {
          const auto &[x0, y0] = std::get<typename Op::Union>(a0.v());
          union_ST(r, n, a, x0, y0);
          _stack.emplace_back(_call{crane_raw(a1)});
        } else {
          const auto &[x0, y0] = std::get<typename Op::Same>(a0.v());
          bool b = same_ST(r, n, a, x0, y0);
          _stack.emplace_back(_after_run_ST_in_Same{b});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_run_ST_in_Same>(_popped));
      _stack.pop_back();
      bool b = _f.b;
      List<bool> bs = std::move(_result);
      _result = List<bool>::cons(b, std::move(bs));
    }
  }
  return _result;
}

List<bool> union_find_ST(STRefs r, uint64_t n, const List<Op> &ops) {
  std::shared_ptr<crane::array_storage<std::pair<uint64_t, uint64_t>>> a =
      make_ST(r, n);
  return run_ST(r, n, std::span{*a}, ops);
}

node get(const NatMap::template bst<std::pair<uint64_t, uint64_t>> &s,
         uint64_t x) {
  auto _cs = NatMap::template find<node>(x, s);
  if (_cs.has_value()) {
    const std::pair<uint64_t, uint64_t> &nd = *_cs;
    return nd;
  } else {
    return std::make_pair(x, UINT64_C(0));
  }
}

std::pair<uint64_t, uf>
find_fun(uint64_t fuel,
         const NatMap::template bst<std::pair<uint64_t, uint64_t>> &s,
         uint64_t x) {
  // Explicit stack replaces the non-tail recursion of find_fun: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t x;
    uint64_t fuel;
  };

  struct _after_find_fun_in_false {
    uint64_t x;
    uint64_t k;
  };

  using _frame = std::variant<_call, _after_find_fun_in_false>;
  std::pair<uint64_t, uf> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{x, fuel});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t x = _f.x;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::make_pair(x, s);
      } else {
        uint64_t fuel_ = fuel - 1;
        auto [p, k] = get(s, x);
        if (p == x) {
          _result = std::make_pair(x, s);
        } else {
          _stack.emplace_back(_after_find_fun_in_false{x, k});
          _stack.emplace_back(_call{p, fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_find_fun_in_false>(_popped));
      _stack.pop_back();
      uint64_t x = _f.x;
      uint64_t k = _f.k;
      auto [r, s_] = std::move(_result);
      _result =
          std::make_pair(r, NatMap::template add<std::pair<uint64_t, uint64_t>>(
                                x, std::make_pair(r, k), std::move(s_)));
    }
  }
  return _result;
}

uf union_fun(uint64_t n,
             const NatMap::template bst<std::pair<uint64_t, uint64_t>> &s,
             uint64_t x, uint64_t y) {
  auto [rx, s0] = find_fun(n, s, x);
  auto [ry, s1] = find_fun(n, std::move(s0), y);
  if (rx == ry) {
    return std::move(s1);
  } else {
    auto [_, kx] = get(s1, rx);
    auto [_, ky] = get(s1, ry);
    if (kx < ky) {
      return NatMap::template add<std::pair<uint64_t, uint64_t>>(
          rx, std::make_pair(ry, kx), std::move(s1));
    } else if (ky < kx) {
      return NatMap::template add<std::pair<uint64_t, uint64_t>>(
          ry, std::make_pair(rx, ky), std::move(s1));
    } else {
      return NatMap::template add<std::pair<uint64_t, uint64_t>>(
          rx, std::make_pair(rx, (kx + 1)),
          NatMap::template add<std::pair<uint64_t, uint64_t>>(
              ry, std::make_pair(rx, ky), std::move(s1)));
    }
  }
}

std::pair<bool, uf>
same_fun(uint64_t n,
         const NatMap::template bst<std::pair<uint64_t, uint64_t>> &s,
         uint64_t x, uint64_t y) {
  auto [rx, s0] = find_fun(n, s, x);
  auto [ry, s1] = find_fun(n, std::move(s0), y);
  return std::make_pair(rx == ry, std::move(s1));
}

List<bool> run_fun(uint64_t n,
                   const NatMap::template bst<std::pair<uint64_t, uint64_t>> &s,
                   const List<Op> &ops) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<List<bool>> _root{};
  std::shared_ptr<List<bool>> *_write = nullptr;
  const List<Op> *_loop_ops = &ops;
  NatMap::template bst<std::pair<uint64_t, uint64_t>> _loop_s = s;
  while (true) {
    if (std::holds_alternative<typename List<Op>::Nil>(_loop_ops->v())) {
      auto _value = List<bool>::nil();
      (_write ? *(*_write = std::make_shared<List<bool>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] = std::get<typename List<Op>::Cons>(_loop_ops->v());
      if (std::holds_alternative<typename Op::Union>(a0.v())) {
        const auto &[x0, y0] = std::get<typename Op::Union>(a0.v());
        _loop_ops = crane_raw(a1);
        _loop_s = union_fun(n, _loop_s, x0, y0);
        continue;
      } else {
        const auto &[x0, y0] = std::get<typename Op::Same>(a0.v());
        auto [b, s0] = same_fun(n, _loop_s, x0, y0);
        auto _cell = typename List<bool>::Cons(b, nullptr);
        List<bool> &_node = (
            _write ? *(*_write = std::make_shared<List<bool>>(std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<bool>::Cons>(_node.v_mut()).l;
        _loop_ops = crane_raw(a1);
        _loop_s = std::move(s0);
        continue;
      }
    }
  }
  return std::move(*_root);
}

List<bool> UnionFind::union_find_ST(uint64_t x0_, const List<Op> &x1_) {
  return ::union_find_ST(STRefs::BUILD_STREFS, x0_, x1_);
}

List<bool> UnionFind::union_find_fun(uint64_t n, const List<Op> &ops) {
  return run_fun(n, empty_uf, ops);
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
