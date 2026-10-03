#include "loopify_advanced_patterns.h"

uint64_t LoopifyAdvancedPatterns::len_impl(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Cont_Cons: resumes after recursive call, then processes rest.
  struct _Cont_Cons {};

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified len_impl: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      _result = (UINT64_C(1) + std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyAdvancedPatterns::as_guard(const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (UINT64_C(3) < len_impl(*_loop_l)) {
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = crane_raw(a1);
        continue;
      } else {
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_head);
}

uint64_t LoopifyAdvancedPatterns::multi_guard(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Cont1: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont1 {
    uint64_t a0;
  };

  /// _Cont2: resumes after recursive call, then processes rest.
  struct _Cont2 {};

  using _Frame = std::variant<_Enter, _Cont1, _Cont2>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified multi_guard: _Enter -> _Cont1 -> _Cont2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        if (UINT64_C(10) < a0) {
          _stack.emplace_back(_Cont1{a0});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else {
          if (UINT64_C(0) < a0) {
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            _stack.emplace_back(_Cont2{});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        }
      }
    } else if (std::holds_alternative<_Cont1>(_frame)) {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t a0 = _f.a0;
      _result = (a0 + std::move(_result));
    } else {
      auto _f = std::move(std::get<_Cont2>(_frame));
      _result = (UINT64_C(1) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyAdvancedPatterns::four_elem(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0, a00, a01, a02], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Cons {
    uint64_t a0;
    uint64_t a00;
    uint64_t a01;
    uint64_t a02;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified four_elem: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        auto &&_sv0 = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
          _result = UINT64_C(1);
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(_sv0.v());
          auto &&_sv1 = *a10;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv1.v())) {
            _result = UINT64_C(2);
          } else {
            const auto &[a01, a11] =
                std::get<typename List<uint64_t>::Cons>(_sv1.v());
            auto &&_sv2 = *a11;
            if (std::holds_alternative<typename List<uint64_t>::Nil>(
                    _sv2.v())) {
              _result = UINT64_C(3);
            } else {
              const auto &[a02, a12] =
                  std::get<typename List<uint64_t>::Cons>(_sv2.v());
              _stack.emplace_back(_Cont_Cons{a0, a00, a01, a02});
              _stack.emplace_back(_Enter{crane_raw(a12)});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t a00 = _f.a00;
      uint64_t a01 = _f.a01;
      uint64_t a02 = _f.a02;
      _result = ((((a0 + a00) + a01) + a02) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyAdvancedPatterns::nested_pattern(
    const List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>> *l;
  };

  /// _Cont_a: saves [a, b, c], resumes after recursive call, then processes
  /// rest.
  struct _Cont_a {
    uint64_t a;
    uint64_t b;
    uint64_t c;
  };

  using _Frame = std::variant<_Enter, _Cont_a>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified nested_pattern: _Enter -> _Cont_a.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<std::pair<std::pair<uint64_t, uint64_t>, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<typename List<
              std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<
            std::pair<std::pair<uint64_t, uint64_t>, uint64_t>>::Cons>(l.v());
        const auto &[p0, c] = a0;
        const auto &[a, b] = p0;
        _stack.emplace_back(_Cont_a{a, b, c});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_a>(_frame));
      uint64_t a = _f.a;
      uint64_t b = _f.b;
      uint64_t c = _f.c;
      _result = (((a + b) + c) + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyAdvancedPatterns::guard_accum(uint64_t acc,
                                              const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_acc = std::move(acc);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (UINT64_C(100) < a0) {
        _loop_l = crane_raw(a1);
        _loop_acc = (_loop_acc * UINT64_C(2));
      } else {
        if (UINT64_C(50) < a0) {
          _loop_l = crane_raw(a1);
          _loop_acc = (_loop_acc + a0);
        } else {
          if (UINT64_C(0) < a0) {
            _loop_l = crane_raw(a1);
            _loop_acc = (_loop_acc + UINT64_C(1));
          } else {
            _loop_l = crane_raw(a1);
          }
        }
      }
    }
  }
}

List<uint64_t> LoopifyAdvancedPatterns::cons_computed(uint64_t n,
                                                      const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      uint64_t next_n;
      if (UINT64_C(0) < _loop_n) {
        next_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
      } else {
        next_n = _loop_n;
      }
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(a0, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_l = crane_raw(a1);
      _loop_n = next_n;
      continue;
    }
  }
  return std::move(*_head);
}

uint64_t LoopifyAdvancedPatterns::extract_value(
    const LoopifyAdvancedPatterns::shape &s) {
  if (std::holds_alternative<typename LoopifyAdvancedPatterns::shape::Circle>(
          s.v())) {
    const auto &[a0] =
        std::get<typename LoopifyAdvancedPatterns::shape::Circle>(s.v());
    return a0;
  } else if (std::holds_alternative<
                 typename LoopifyAdvancedPatterns::shape::Square>(s.v())) {
    const auto &[a0] =
        std::get<typename LoopifyAdvancedPatterns::shape::Square>(s.v());
    return a0;
  } else {
    const auto &[a0] =
        std::get<typename LoopifyAdvancedPatterns::shape::Triangle>(s.v());
    return a0;
  }
}

uint64_t LoopifyAdvancedPatterns::sum_shapes(
    const List<LoopifyAdvancedPatterns::shape>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyAdvancedPatterns::shape> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    LoopifyAdvancedPatterns::shape a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_shapes: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyAdvancedPatterns::shape> &l = *_f.l;
      if (std::holds_alternative<
              typename List<LoopifyAdvancedPatterns::shape>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyAdvancedPatterns::shape>::Cons>(
                l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      LoopifyAdvancedPatterns::shape a0 = std::move(_f.a0);
      _result = (extract_value(a0) + std::move(_result));
    }
  }
  return _result;
}

std::pair<std::pair<uint64_t, uint64_t>, uint64_t>
LoopifyAdvancedPatterns::count_by_shape(
    const List<LoopifyAdvancedPatterns::shape>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyAdvancedPatterns::shape> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    LoopifyAdvancedPatterns::shape a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<std::pair<uint64_t, uint64_t>, uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&l});
  /// Loopified count_by_shape: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyAdvancedPatterns::shape> &l = *_f.l;
      if (std::holds_alternative<
              typename List<LoopifyAdvancedPatterns::shape>::Nil>(l.v())) {
        _result = std::make_pair(std::make_pair(UINT64_C(0), UINT64_C(0)),
                                 UINT64_C(0));
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyAdvancedPatterns::shape>::Cons>(
                l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      LoopifyAdvancedPatterns::shape a0 = std::move(_f.a0);
      auto [p, triangles] = std::move(_result);
      auto [circles, squares] = std::move(p);
      if (std::holds_alternative<
              typename LoopifyAdvancedPatterns::shape::Circle>(a0.v())) {
        _result = std::make_pair(
            std::make_pair((circles + UINT64_C(1)), squares), triangles);
      } else if (std::holds_alternative<
                     typename LoopifyAdvancedPatterns::shape::Square>(a0.v())) {
        _result = std::make_pair(
            std::make_pair(circles, (squares + UINT64_C(1))), triangles);
      } else {
        _result = std::make_pair(std::make_pair(circles, squares),
                                 (triangles + UINT64_C(1)));
      }
    }
  }
  return _result;
}

List<uint64_t> LoopifyAdvancedPatterns::replace_at(uint64_t idx, uint64_t value,
                                                   const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_idx = std::move(idx);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (_loop_idx == UINT64_C(0)) {
        *_write =
            std::make_shared<List<uint64_t>>(List<uint64_t>::cons(value, *a1));
        break;
      } else {
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = crane_raw(a1);
        _loop_idx = (((_loop_idx - UINT64_C(1)) > _loop_idx
                          ? 0
                          : (_loop_idx - UINT64_C(1))));
        continue;
      }
    }
  }
  return std::move(*_head);
}
