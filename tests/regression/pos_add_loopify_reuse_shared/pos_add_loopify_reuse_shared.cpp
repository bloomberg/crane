#include "pos_add_loopify_reuse_shared.h"

Positive Coq_Pos::succ(const Positive &x) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto pos_2 = crane::immortal(Positive::xo(Positive::xh()));
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<Positive> _root{};
  crane::shared_box<Positive> *_write = nullptr;
  const Positive *_loop_x = &x;
  while (true) {
    if (crane::holds_alternative<typename Positive::XI>(_loop_x->v())) {
      const auto &[a0] = crane::get<typename Positive::XI>(_loop_x->v());
      auto _cell = typename Positive::XO(nullptr);
      Positive &_node = (_write ? *(*_write = crane::shared_box<Positive>::make(
                                        std::move(_cell)))
                                : _root.emplace(std::move(_cell)));
      _write = &crane::get<typename Positive::XO>(_node.v_mut()).a0;
      _loop_x = crane_raw(a0);
      continue;
    } else if (crane::holds_alternative<typename Positive::XO>(_loop_x->v())) {
      const auto &[a0] = crane::get<typename Positive::XO>(_loop_x->v());
      auto _value = Positive::xi(*a0);
      (_write ? *(*_write =
                      crane::shared_box<Positive>::make(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      auto _value = pos_2;
      (_write ? *(*_write =
                      crane::shared_box<Positive>::make(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    }
  }
  return std::move(*_root);
}

Positive Coq_Pos::add(const Positive &x, const Positive &y) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto pos_2 = crane::immortal(Positive::xo(Positive::xh()));
  static const auto pos_3 = crane::immortal(Positive::xi(Positive::xh()));

  // Explicit stack replaces the non-tail recursion of add: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const Positive *y;
    const Positive *x;
  };

  struct _call_add_carry_entry {
    Positive y0;
    Positive x0;
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
    if (crane::holds_alternative<_call>(_popped)) {
      auto _f = std::move(crane::get<_call>(_popped));
      _stack.pop_back();
      const Positive &y = *_f.y;
      const Positive &x = *_f.x;
      if (crane::holds_alternative<typename Positive::XI>(x.v())) {
        const auto &[a00] = crane::get<typename Positive::XI>(x.v());
        if (crane::holds_alternative<typename Positive::XI>(y.v())) {
          const auto &[a01] = crane::get<typename Positive::XI>(y.v());
          _stack.emplace_back(_after_add_carry_entry_in_XI{});
          _stack.emplace_back(_call_add_carry_entry{*a01, *a00});
        } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
          const auto &[a01] = crane::get<typename Positive::XO>(y.v());
          _stack.emplace_back(_after_add_in_XO{});
          _stack.emplace_back(_call{crane_raw(a01), crane_raw(a00)});
        } else {
          _result = Positive::xo(succ(*a00));
        }
      } else if (crane::holds_alternative<typename Positive::XO>(x.v())) {
        const auto &[a00] = crane::get<typename Positive::XO>(x.v());
        if (crane::holds_alternative<typename Positive::XI>(y.v())) {
          const auto &[a01] = crane::get<typename Positive::XI>(y.v());
          _stack.emplace_back(_after_add_in_XI{});
          _stack.emplace_back(_call{crane_raw(a01), crane_raw(a00)});
        } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
          const auto &[a01] = crane::get<typename Positive::XO>(y.v());
          _stack.emplace_back(_after_add_in_XO_2{});
          _stack.emplace_back(_call{crane_raw(a01), crane_raw(a00)});
        } else {
          _result = Positive::xi(*a00);
        }
      } else {
        if (crane::holds_alternative<typename Positive::XI>(y.v())) {
          const auto &[a01] = crane::get<typename Positive::XI>(y.v());
          _result = Positive::xo(succ(*a01));
        } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
          const auto &[a01] = crane::get<typename Positive::XO>(y.v());
          _result = Positive::xi(*a01);
        } else {
          _result = pos_2;
        }
      }
    } else if (crane::holds_alternative<_call_add_carry_entry>(_popped)) {
      auto _f = std::move(crane::get<_call_add_carry_entry>(_popped));
      _stack.pop_back();
      Positive y0 = std::move(_f.y0);
      Positive x0 = std::move(_f.x0);
      if (crane::holds_alternative<typename Positive::XI>(x0.v())) {
        const auto &[a0] = crane::get<typename Positive::XI>(x0.v());
        if (crane::holds_alternative<typename Positive::XI>(y0.v())) {
          const auto &[a00] = crane::get<typename Positive::XI>(y0.v());
          _stack.emplace_back(_after_add_carry_entry_in_XI_2{});
          _stack.emplace_back(_call_add_carry_entry{*a00, *a0});
        } else if (crane::holds_alternative<typename Positive::XO>(y0.v())) {
          const auto &[a00] = crane::get<typename Positive::XO>(y0.v());
          _stack.emplace_back(_after_add_carry_entry_in_XO{});
          _stack.emplace_back(_call_add_carry_entry{*a00, *a0});
        } else {
          _result = Positive::xi(succ(*a0));
        }
      } else if (crane::holds_alternative<typename Positive::XO>(x0.v())) {
        const auto &[a0] = crane::get<typename Positive::XO>(x0.v());
        if (crane::holds_alternative<typename Positive::XI>(y0.v())) {
          const auto &[a00] = crane::get<typename Positive::XI>(y0.v());
          _stack.emplace_back(_after_add_carry_entry_in_XI_3{});
          _stack.emplace_back(_call_add_carry_entry{*a00, *a0});
        } else if (crane::holds_alternative<typename Positive::XO>(y0.v())) {
          const auto &[a00] = crane::get<typename Positive::XO>(y0.v());
          _stack.emplace_back(_after_add_in_XO_3{});
          _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
        } else {
          _result = Positive::xo(succ(*a0));
        }
      } else {
        if (crane::holds_alternative<typename Positive::XI>(y0.v())) {
          const auto &[a00] = crane::get<typename Positive::XI>(y0.v());
          _result = Positive::xi(succ(*a00));
        } else if (crane::holds_alternative<typename Positive::XO>(y0.v())) {
          const auto &[a00] = crane::get<typename Positive::XO>(y0.v());
          _result = Positive::xo(succ(*a00));
        } else {
          _result = pos_3;
        }
      }
    } else if (crane::holds_alternative<_after_add_carry_entry_in_XI>(_popped)) {
      auto _f = std::move(crane::get<_after_add_carry_entry_in_XI>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    } else if (
                   crane::holds_alternative<_after_add_carry_entry_in_XI_2>(
                       _popped)) {
      auto _f = std::move(crane::get<_after_add_carry_entry_in_XI_2>(_popped));
      _stack.pop_back();
      _result = Positive::xi(std::move(_result));
    } else if (
                   crane::holds_alternative<_after_add_carry_entry_in_XI_3>(
                       _popped)) {
      auto _f = std::move(crane::get<_after_add_carry_entry_in_XI_3>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    } else if (crane::holds_alternative<_after_add_carry_entry_in_XO>(_popped)) {
      auto _f = std::move(crane::get<_after_add_carry_entry_in_XO>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    } else if (crane::holds_alternative<_after_add_in_XI>(_popped)) {
      auto _f = std::move(crane::get<_after_add_in_XI>(_popped));
      _stack.pop_back();
      _result = Positive::xi(std::move(_result));
    } else if (crane::holds_alternative<_after_add_in_XO>(_popped)) {
      auto _f = std::move(crane::get<_after_add_in_XO>(_popped));
      _stack.pop_back();
      _result = Positive::xi(std::move(_result));
    } else if (crane::holds_alternative<_after_add_in_XO_2>(_popped)) {
      auto _f = std::move(crane::get<_after_add_in_XO_2>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    } else {
      auto _f = std::move(crane::get<_after_add_in_XO_3>(_popped));
      _stack.pop_back();
      _result = Positive::xi(std::move(_result));
    }
  }
  return _result;
}

Positive Coq_Pos::add_carry(const Positive &x, const Positive &y) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto pos_3 = crane::immortal(Positive::xi(Positive::xh()));
  static const auto pos_2 = crane::immortal(Positive::xo(Positive::xh()));

  // Explicit stack replaces the non-tail recursion of add_carry: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const Positive *y;
    const Positive *x;
  };

  struct _call_add_entry {
    Positive y0;
    Positive x0;
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
    if (crane::holds_alternative<_call>(_popped)) {
      auto _f = std::move(crane::get<_call>(_popped));
      _stack.pop_back();
      const Positive &y = *_f.y;
      const Positive &x = *_f.x;
      if (crane::holds_alternative<typename Positive::XI>(x.v())) {
        const auto &[a00] = crane::get<typename Positive::XI>(x.v());
        if (crane::holds_alternative<typename Positive::XI>(y.v())) {
          const auto &[a01] = crane::get<typename Positive::XI>(y.v());
          _stack.emplace_back(_after_add_carry_in_XI{});
          _stack.emplace_back(_call{crane_raw(a01), crane_raw(a00)});
        } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
          const auto &[a01] = crane::get<typename Positive::XO>(y.v());
          _stack.emplace_back(_after_add_carry_in_XO{});
          _stack.emplace_back(_call{crane_raw(a01), crane_raw(a00)});
        } else {
          _result = Positive::xi(succ(*a00));
        }
      } else if (crane::holds_alternative<typename Positive::XO>(x.v())) {
        const auto &[a00] = crane::get<typename Positive::XO>(x.v());
        if (crane::holds_alternative<typename Positive::XI>(y.v())) {
          const auto &[a01] = crane::get<typename Positive::XI>(y.v());
          _stack.emplace_back(_after_add_carry_in_XI_2{});
          _stack.emplace_back(_call{crane_raw(a01), crane_raw(a00)});
        } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
          const auto &[a01] = crane::get<typename Positive::XO>(y.v());
          _stack.emplace_back(_after_add_entry_in_XO{});
          _stack.emplace_back(_call_add_entry{*a01, *a00});
        } else {
          _result = Positive::xo(succ(*a00));
        }
      } else {
        if (crane::holds_alternative<typename Positive::XI>(y.v())) {
          const auto &[a01] = crane::get<typename Positive::XI>(y.v());
          _result = Positive::xi(succ(*a01));
        } else if (crane::holds_alternative<typename Positive::XO>(y.v())) {
          const auto &[a01] = crane::get<typename Positive::XO>(y.v());
          _result = Positive::xo(succ(*a01));
        } else {
          _result = pos_3;
        }
      }
    } else if (crane::holds_alternative<_call_add_entry>(_popped)) {
      auto _f = std::move(crane::get<_call_add_entry>(_popped));
      _stack.pop_back();
      Positive y0 = std::move(_f.y0);
      Positive x0 = std::move(_f.x0);
      if (crane::holds_alternative<typename Positive::XI>(x0.v())) {
        const auto &[a0] = crane::get<typename Positive::XI>(x0.v());
        if (crane::holds_alternative<typename Positive::XI>(y0.v())) {
          const auto &[a00] = crane::get<typename Positive::XI>(y0.v());
          _stack.emplace_back(_after_add_carry_in_XI_3{});
          _stack.emplace_back(_call{crane_raw(a00), crane_raw(a0)});
        } else if (crane::holds_alternative<typename Positive::XO>(y0.v())) {
          const auto &[a00] = crane::get<typename Positive::XO>(y0.v());
          _stack.emplace_back(_after_add_entry_in_XO_2{});
          _stack.emplace_back(_call_add_entry{*a00, *a0});
        } else {
          _result = Positive::xo(succ(*a0));
        }
      } else if (crane::holds_alternative<typename Positive::XO>(x0.v())) {
        const auto &[a0] = crane::get<typename Positive::XO>(x0.v());
        if (crane::holds_alternative<typename Positive::XI>(y0.v())) {
          const auto &[a00] = crane::get<typename Positive::XI>(y0.v());
          _stack.emplace_back(_after_add_entry_in_XI{});
          _stack.emplace_back(_call_add_entry{*a00, *a0});
        } else if (crane::holds_alternative<typename Positive::XO>(y0.v())) {
          const auto &[a00] = crane::get<typename Positive::XO>(y0.v());
          _stack.emplace_back(_after_add_entry_in_XO_3{});
          _stack.emplace_back(_call_add_entry{*a00, *a0});
        } else {
          _result = Positive::xi(*a0);
        }
      } else {
        if (crane::holds_alternative<typename Positive::XI>(y0.v())) {
          const auto &[a00] = crane::get<typename Positive::XI>(y0.v());
          _result = Positive::xo(succ(*a00));
        } else if (crane::holds_alternative<typename Positive::XO>(y0.v())) {
          const auto &[a00] = crane::get<typename Positive::XO>(y0.v());
          _result = Positive::xi(*a00);
        } else {
          _result = pos_2;
        }
      }
    } else if (crane::holds_alternative<_after_add_carry_in_XI>(_popped)) {
      auto _f = std::move(crane::get<_after_add_carry_in_XI>(_popped));
      _stack.pop_back();
      _result = Positive::xi(std::move(_result));
    } else if (crane::holds_alternative<_after_add_carry_in_XI_2>(_popped)) {
      auto _f = std::move(crane::get<_after_add_carry_in_XI_2>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    } else if (crane::holds_alternative<_after_add_carry_in_XI_3>(_popped)) {
      auto _f = std::move(crane::get<_after_add_carry_in_XI_3>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    } else if (crane::holds_alternative<_after_add_carry_in_XO>(_popped)) {
      auto _f = std::move(crane::get<_after_add_carry_in_XO>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    } else if (crane::holds_alternative<_after_add_entry_in_XI>(_popped)) {
      auto _f = std::move(crane::get<_after_add_entry_in_XI>(_popped));
      _stack.pop_back();
      _result = Positive::xi(std::move(_result));
    } else if (crane::holds_alternative<_after_add_entry_in_XO>(_popped)) {
      auto _f = std::move(crane::get<_after_add_entry_in_XO>(_popped));
      _stack.pop_back();
      _result = Positive::xi(std::move(_result));
    } else if (crane::holds_alternative<_after_add_entry_in_XO_2>(_popped)) {
      auto _f = std::move(crane::get<_after_add_entry_in_XO_2>(_popped));
      _stack.pop_back();
      _result = Positive::xi(std::move(_result));
    } else {
      auto _f = std::move(crane::get<_after_add_entry_in_XO_3>(_popped));
      _stack.pop_back();
      _result = Positive::xo(std::move(_result));
    }
  }
  return _result;
}

uint64_t Coq_Pos::to_nat(const Positive &x) {
  return iter_op<uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
      x,
      UINT64_C(1));
}

Positive Coq_Pos::of_succ_nat(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of of_succ_nat: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_of_succ_nat_in_S {};

  using _frame = std::variant<_call, _after_of_succ_nat_in_S>;
  Positive _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (crane::holds_alternative<_call>(_popped)) {
      auto _f = std::move(crane::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = Positive::xh();
      } else {
        uint64_t x = n - 1;
        _stack.emplace_back(_after_of_succ_nat_in_S{});
        _stack.emplace_back(_call{x});
      }
    } else {
      auto _f = std::move(crane::get<_after_of_succ_nat_in_S>(_popped));
      _stack.pop_back();
      _result = succ(std::move(_result));
    }
  }
  return _result;
}

Positive Pos::succ(const Positive &x) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto pos_2 = crane::immortal(Positive::xo(Positive::xh()));
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<Positive> _root{};
  crane::shared_box<Positive> *_write = nullptr;
  const Positive *_loop_x = &x;
  while (true) {
    if (crane::holds_alternative<typename Positive::XI>(_loop_x->v())) {
      const auto &[a0] = crane::get<typename Positive::XI>(_loop_x->v());
      auto _cell = typename Positive::XO(nullptr);
      Positive &_node = (_write ? *(*_write = crane::shared_box<Positive>::make(
                                        std::move(_cell)))
                                : _root.emplace(std::move(_cell)));
      _write = &crane::get<typename Positive::XO>(_node.v_mut()).a0;
      _loop_x = crane_raw(a0);
      continue;
    } else if (crane::holds_alternative<typename Positive::XO>(_loop_x->v())) {
      const auto &[a0] = crane::get<typename Positive::XO>(_loop_x->v());
      auto _value = Positive::xi(*a0);
      (_write ? *(*_write =
                      crane::shared_box<Positive>::make(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      auto _value = pos_2;
      (_write ? *(*_write =
                      crane::shared_box<Positive>::make(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    }
  }
  return std::move(*_root);
}

uint64_t Pos::to_nat(const Positive &x) {
  return iter_op<uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
      x,
      UINT64_C(1));
}

Positive Pos::of_succ_nat(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of of_succ_nat: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_of_succ_nat_in_S {};

  using _frame = std::variant<_call, _after_of_succ_nat_in_S>;
  Positive _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (crane::holds_alternative<_call>(_popped)) {
      auto _f = std::move(crane::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = Positive::xh();
      } else {
        uint64_t x = n - 1;
        _stack.emplace_back(_after_of_succ_nat_in_S{});
        _stack.emplace_back(_call{x});
      }
    } else {
      auto _f = std::move(crane::get<_after_of_succ_nat_in_S>(_popped));
      _stack.pop_back();
      _result = succ(std::move(_result));
    }
  }
  return _result;
}

N BinNat::add(N n, N m) {
  if (crane::holds_alternative<typename N::N0>(n.v())) {
    return m;
  } else {
    const auto &[a0] = crane::get<typename N::Npos>(n.v());
    // Reuse the matched cell in place when this is its only owner; otherwise
    // rebuild.
    if (m.v().index() == 1) {
      if (m.v().unique()) {
        Positive q = std::move(crane::get<typename N::Npos>(m.v_mut()).a0);
        return N::npos_crane_reuse(std::move(m),
                                   Coq_Pos::add(a0, std::move(q)));
      } else {
        if (crane::holds_alternative<typename N::N0>(m.v())) {
          return n;
        } else {
          const auto &[a00] = crane::get<typename N::Npos>(m.v());
          return N::npos(Coq_Pos::add(a0, a00));
        }
      }
    } else {
      if (crane::holds_alternative<typename N::N0>(m.v())) {
        return n;
      } else {
        const auto &[a00] = crane::get<typename N::Npos>(m.v());
        return N::npos(Coq_Pos::add(a0, a00));
      }
    }
  }
}

uint64_t BinNat::to_nat(const N &a0) {
  if (crane::holds_alternative<typename N::N0>(a0.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a1] = crane::get<typename N::Npos>(a0.v());
    return Pos::to_nat(a1);
  }
}

N BinNat::of_nat(uint64_t n) {
  if (n <= 0) {
    return N::n0();
  } else {
    uint64_t n_ = n - 1;
    return N::npos(Pos::of_succ_nat(n_));
  }
}

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Was a wrong value, no diagnostic.  With Loopify, Reuse and SharedVariant
/// all on (any two were fine), Stdlib's Pos.add 9 19 was 20 in C++
/// instead of 28 (so N.add 9 19 too, without any N mapping);
/// Pos.add 1 1, Pos.add 3 1, Pos.succ 7 were right.  No sanitizer
/// report.
///
/// The mutually recursive Pos.add/Pos.add_carry run as one machine,
/// add_carry adopted as an entry taking its arguments by value.  Its
/// handler matched them through v_mut(), which copies a shared block, and
/// pushed a _call of add pointing into the copy's fields; the copy died
/// with the handler and the pool gave its memory to the next block.
/// Sums of positives built at run time, so held once, across every carry.
uint64_t PosAddLoopifyReuseShared::pos_add(uint64_t x, uint64_t y) {
  return Coq_Pos::to_nat(
      Coq_Pos::add(Coq_Pos::of_succ_nat(x), Coq_Pos::of_succ_nat(y)));
}

uint64_t PosAddLoopifyReuseShared::pos_add_carry(uint64_t x, uint64_t y) {
  return Coq_Pos::to_nat(
      Coq_Pos::add_carry(Coq_Pos::of_succ_nat(x), Coq_Pos::of_succ_nat(y)));
}

uint64_t PosAddLoopifyReuseShared::n_add(uint64_t x, uint64_t y) {
  return BinNat::to_nat(BinNat::add(BinNat::of_nat(x), BinNat::of_nat(y)));
}
