#include <loopify_advanced_patterns.h>

unsigned int LoopifyAdvancedPatterns::len_impl(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Loopified len_impl: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{1u});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

List<unsigned int>
LoopifyAdvancedPatterns::as_guard(const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (3u < len_impl(*(_loop_l))) {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = d_a1.get();
        continue;
      } else {
        _loop_l = d_a1.get();
        continue;
      }
    }
  }
  return std::move(*(_head));
}

unsigned int LoopifyAdvancedPatterns::multi_guard(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Resume1: saves [d_a0], resumes after recursive call with _result.
  struct _Resume1 {
    unsigned int d_a0;
  };

  /// _Resume2: saves [_s0], resumes after recursive call with _result.
  struct _Resume2 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Loopified multi_guard: _Enter -> _Resume1 -> _Resume2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        if (10u < d_a0) {
          _stack.emplace_back(_Resume1{d_a0});
          _stack.emplace_back(_Enter{d_a1.get()});
        } else {
          if (0u < d_a0) {
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            _stack.emplace_back(_Resume2{1u});
            _stack.emplace_back(_Enter{d_a1.get()});
          }
        }
      }
    } else if (std::holds_alternative<_Resume1>(_frame)) {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.d_a0 + _result);
    } else {
      auto _f = std::move(std::get<_Resume2>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

unsigned int LoopifyAdvancedPatterns::four_elem(
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype((
        ((std::declval<unsigned int &>() + std::declval<unsigned int &>()) +
         std::declval<unsigned int &>()) +
        std::declval<unsigned int &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Loopified four_elem: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        auto &&_sv0 = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0.v())) {
          _result = 1u;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_sv0.v());
          auto &&_sv1 = *(d_a10);
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv1.v())) {
            _result = 2u;
          } else {
            const auto &[d_a01, d_a11] =
                std::get<typename List<unsigned int>::Cons>(_sv1.v());
            auto &&_sv2 = *(d_a11);
            if (std::holds_alternative<typename List<unsigned int>::Nil>(
                    _sv2.v())) {
              _result = 3u;
            } else {
              const auto &[d_a02, d_a12] =
                  std::get<typename List<unsigned int>::Cons>(_sv2.v());
              _stack.emplace_back(
                  _Resume_Cons{(((d_a0 + d_a00) + d_a01) + d_a02)});
              _stack.emplace_back(_Enter{d_a12.get()});
            }
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

unsigned int LoopifyAdvancedPatterns::nested_pattern(
    const List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>
        *l;
  };

  /// _Resume_a: saves [_s0], resumes after recursive call with _result.
  struct _Resume_a {
    decltype((
        (std::declval<unsigned int &>() + std::declval<unsigned int &>()) +
        std::declval<unsigned int &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_a>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Loopified nested_pattern: _Enter -> _Resume_a.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>
          &l = *(_f.l);
      if (std::holds_alternative<typename List<std::pair<
              std::pair<unsigned int, unsigned int>, unsigned int>>::Nil>(
              l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<std::pair<
            std::pair<unsigned int, unsigned int>, unsigned int>>::Cons>(l.v());
        const std::pair<unsigned int, unsigned int> &p0 = d_a0.first;
        const unsigned int &c = d_a0.second;
        const unsigned int &a = p0.first;
        const unsigned int &b = p0.second;
        _stack.emplace_back(_Resume_a{((a + b) + c)});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_a>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

unsigned int LoopifyAdvancedPatterns::guard_accum(const unsigned int acc,
                                                  const List<unsigned int> &l) {
  unsigned int _result;
  const List<unsigned int> *_loop_l = &l;
  unsigned int _loop_acc = acc;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = _loop_acc;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (100u < d_a0) {
        _loop_l = d_a1.get();
        _loop_acc = (_loop_acc * 2u);
      } else {
        if (50u < d_a0) {
          _loop_l = d_a1.get();
          _loop_acc = (_loop_acc + d_a0);
        } else {
          if (0u < d_a0) {
            _loop_l = d_a1.get();
            _loop_acc = (_loop_acc + 1u);
          } else {
            _loop_l = d_a1.get();
          }
        }
      }
    }
  }
  return _result;
}

List<unsigned int>
LoopifyAdvancedPatterns::cons_computed(const unsigned int n,
                                       const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  unsigned int _loop_n = n;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      unsigned int next_n;
      if (0u < _loop_n) {
        next_n = (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
      } else {
        next_n = _loop_n;
      }
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(d_a0, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      _loop_l = d_a1.get();
      _loop_n = next_n;
      continue;
    }
  }
  return std::move(*(_head));
}

unsigned int LoopifyAdvancedPatterns::extract_value(
    const LoopifyAdvancedPatterns::shape &s) {
  if (std::holds_alternative<typename LoopifyAdvancedPatterns::shape::Circle>(
          s.v())) {
    const auto &[d_a0] =
        std::get<typename LoopifyAdvancedPatterns::shape::Circle>(s.v());
    return d_a0;
  } else if (std::holds_alternative<
                 typename LoopifyAdvancedPatterns::shape::Square>(s.v())) {
    const auto &[d_a0] =
        std::get<typename LoopifyAdvancedPatterns::shape::Square>(s.v());
    return d_a0;
  } else {
    const auto &[d_a0] =
        std::get<typename LoopifyAdvancedPatterns::shape::Triangle>(s.v());
    return d_a0;
  }
}

unsigned int LoopifyAdvancedPatterns::sum_shapes(
    const List<LoopifyAdvancedPatterns::shape>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyAdvancedPatterns::shape> *l;
  };

  /// _Resume_Cons: saves [d_a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(extract_value(
        std::declval<LoopifyAdvancedPatterns::shape &>())) d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_shapes: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyAdvancedPatterns::shape> &l = *(_f.l);
      if (std::holds_alternative<
              typename List<LoopifyAdvancedPatterns::shape>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<LoopifyAdvancedPatterns::shape>::Cons>(
                l.v());
        _stack.emplace_back(_Resume_Cons{extract_value(d_a0)});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.d_a0 + _result);
    }
  }
  return _result;
}

std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
LoopifyAdvancedPatterns::count_by_shape(
    const List<LoopifyAdvancedPatterns::shape>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyAdvancedPatterns::shape> *l;
  };

  /// _Cont_Cons: saves [d_a0], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons {
    LoopifyAdvancedPatterns::shape d_a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<std::pair<unsigned int, unsigned int>, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Loopified count_by_shape: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyAdvancedPatterns::shape> &l = *(_f.l);
      if (std::holds_alternative<
              typename List<LoopifyAdvancedPatterns::shape>::Nil>(l.v())) {
        _result = std::make_pair(std::make_pair(0u, 0u), 0u);
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<LoopifyAdvancedPatterns::shape>::Cons>(
                l.v());
        _stack.emplace_back(_Cont_Cons{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      LoopifyAdvancedPatterns::shape d_a0 = std::move(_f.d_a0);
      const std::pair<unsigned int, unsigned int> &p = _result.first;
      const unsigned int &triangles = _result.second;
      const unsigned int &circles = p.first;
      const unsigned int &squares = p.second;
      if (std::holds_alternative<
              typename LoopifyAdvancedPatterns::shape::Circle>(d_a0.v())) {
        _result =
            std::make_pair(std::make_pair((circles + 1u), squares), triangles);
      } else if (std::holds_alternative<
                     typename LoopifyAdvancedPatterns::shape::Square>(
                     d_a0.v())) {
        _result =
            std::make_pair(std::make_pair(circles, (squares + 1u)), triangles);
      } else {
        _result =
            std::make_pair(std::make_pair(circles, squares), (triangles + 1u));
      }
    }
  }
  return _result;
}

List<unsigned int>
LoopifyAdvancedPatterns::replace_at(const unsigned int idx,
                                    const unsigned int value,
                                    const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  unsigned int _loop_idx = idx;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (_loop_idx == 0u) {
        *(_write) = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(value, *(d_a1)));
        break;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = d_a1.get();
        _loop_idx = (((_loop_idx - 1u) > _loop_idx ? 0 : (_loop_idx - 1u)));
        continue;
      }
    }
  }
  return std::move(*(_head));
}
