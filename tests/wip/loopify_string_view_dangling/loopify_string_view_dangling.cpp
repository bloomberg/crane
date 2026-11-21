#include "loopify_string_view_dangling.h"

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

uint64_t Pos::to_nat(const Positive &x) {
  return iter_op<uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); }, x,
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
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
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
      auto _f = std::move(std::get<_after_of_succ_nat_in_S>(_popped));
      _stack.pop_back();
      _result = succ(std::move(_result));
    }
  }
  return _result;
}

uint64_t BinInt::to_nat(const Z &z) {
  if (std::holds_alternative<typename Z::Zpos>(z.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(z.v());
    return Pos::to_nat(a0);
  } else {
    return UINT64_C(0);
  }
}

Z BinInt::of_nat(uint64_t n) {
  if (n <= 0) {
    return Z::z0();
  } else {
    uint64_t n0 = n - 1;
    return Z::zpos(Pos::of_succ_nat(n0));
  }
}

Z IntDef::double_(const Z &x) {
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

Z IntDef::succ_double(const Z &x) {
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

uint64_t LoopifyStringViewDangling::i2n(int64_t i) {
  return BinInt::to_nat(Uint63Axioms::to_Z(i));
}

int64_t LoopifyStringViewDangling::n2i(uint64_t n) {
  return Uint63Axioms::of_Z(BinInt::of_nat(n));
}

uint64_t LoopifyStringViewDangling::drop_each(const List<bool> &l,
                                              std::string_view s) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  std::string_view _loop_s = s;
  const List<bool> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<bool>::Nil>(_loop_l->v())) {
      return (
          (i2n(static_cast<int64_t>((std::string_view{_loop_s}).size())) *
           UINT64_C(1000)) +
          i2n(crane::string_get(std::string_view{_loop_s}, n2i(UINT64_C(0)))));
    } else {
      const auto &[_, a1] = std::get<typename List<bool>::Cons>(_loop_l->v());
      _loop_s = crane::string_sub(std::string_view{_loop_s}, n2i(UINT64_C(1)),
                                  n2i(UINT64_C(100)));
      _loop_l = crane_raw(a1);
    }
  }
}

bool Uint63Axioms::is_zero(int64_t i) { return i == INT64_C(0); }

bool Uint63Axioms::is_even(int64_t i) {
  return Uint63Axioms::is_zero((i & INT64_C(1)));
}

Z Uint63Axioms::to_Z_rec(uint64_t n, int64_t i) {
  // Explicit stack replaces the non-tail recursion of to_Z_rec: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    int64_t i;
    uint64_t n;
  };

  struct _after_to_Z_rec_in_false {};

  struct _after_to_Z_rec_in_true {};

  using _frame =
      std::variant<_call, _after_to_Z_rec_in_false, _after_to_Z_rec_in_true>;
  Z _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{i, n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      int64_t i = _f.i;
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = Z::z0();
      } else {
        uint64_t n0 = n - 1;
        if (Uint63Axioms::is_even(i)) {
          _stack.emplace_back(_after_to_Z_rec_in_true{});
          _stack.emplace_back(
              _call{(INT64_C(1) >= 63
                         ? 0
                         : static_cast<int64_t>(
                               static_cast<uint64_t>(i) >> (INT64_C(1) & 63))),
                    n0});
        } else {
          _stack.emplace_back(_after_to_Z_rec_in_false{});
          _stack.emplace_back(
              _call{(INT64_C(1) >= 63
                         ? 0
                         : static_cast<int64_t>(
                               static_cast<uint64_t>(i) >> (INT64_C(1) & 63))),
                    n0});
        }
      }
    } else if (std::holds_alternative<_after_to_Z_rec_in_false>(_popped)) {
      auto _f = std::move(std::get<_after_to_Z_rec_in_false>(_popped));
      _stack.pop_back();
      _result = IntDef::succ_double(std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_to_Z_rec_in_true>(_popped));
      _stack.pop_back();
      _result = IntDef::double_(std::move(_result));
    }
  }
  return _result;
}

Z Uint63Axioms::to_Z(int64_t x0_) {
  return Uint63Axioms::to_Z_rec(Uint63Axioms::size, x0_);
}

int64_t Uint63Axioms::of_pos_rec(uint64_t n, const Positive &p) {
  // Explicit stack replaces the non-tail recursion of of_pos_rec: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const Positive *p;
    uint64_t n;
  };

  struct _after_of_pos_rec_in_XI {};

  struct _after_of_pos_rec_in_XO {};

  using _frame =
      std::variant<_call, _after_of_pos_rec_in_XI, _after_of_pos_rec_in_XO>;
  int64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&p, n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const Positive &p = *_f.p;
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = INT64_C(0);
      } else {
        uint64_t n0 = n - 1;
        if (std::holds_alternative<typename Positive::XI>(p.v())) {
          const auto &[a0] = std::get<typename Positive::XI>(p.v());
          _stack.emplace_back(_after_of_pos_rec_in_XI{});
          _stack.emplace_back(_call{crane_raw(a0), n0});
        } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
          const auto &[a0] = std::get<typename Positive::XO>(p.v());
          _stack.emplace_back(_after_of_pos_rec_in_XO{});
          _stack.emplace_back(_call{crane_raw(a0), n0});
        } else {
          _result = INT64_C(1);
        }
      }
    } else if (std::holds_alternative<_after_of_pos_rec_in_XI>(_popped)) {
      auto _f = std::move(std::get<_after_of_pos_rec_in_XI>(_popped));
      _stack.pop_back();
      _result = ((INT64_C(1) >= 63
                      ? 0
                      : static_cast<int64_t>(
                            (static_cast<uint64_t>(std::move(_result)) <<
                             (INT64_C(1) & 63)) &
                            0x7FFFFFFFFFFFFFFFULL)) |
                 INT64_C(1));
    } else {
      auto _f = std::move(std::get<_after_of_pos_rec_in_XO>(_popped));
      _stack.pop_back();
      _result = (INT64_C(1) >= 63
                     ? 0
                     : static_cast<int64_t>(
                           (static_cast<uint64_t>(std::move(_result)) <<
                            (INT64_C(1) & 63)) &
                           0x7FFFFFFFFFFFFFFFULL));
    }
  }
  return _result;
}

int64_t Uint63Axioms::of_pos(const Positive &x0_) {
  return Uint63Axioms::of_pos_rec(Uint63Axioms::size, x0_);
}

int64_t Uint63Axioms::of_Z(const Z &z) {
  if (std::holds_alternative<typename Z::Z0>(z.v())) {
    return INT64_C(0);
  } else if (std::holds_alternative<typename Z::Zpos>(z.v())) {
    const auto &[a0] = std::get<typename Z::Zpos>(z.v());
    return Uint63Axioms::of_pos(a0);
  } else {
    const auto &[a0] = std::get<typename Z::Zneg>(z.v());
    return static_cast<int64_t>(
        (static_cast<uint64_t>(INT64_C(0)) -
         static_cast<uint64_t>(Uint63Axioms::of_pos(a0))) &
        0x7FFFFFFFFFFFFFFFULL);
  }
}
