#include <loopify_advanced_patterns.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

__attribute__((pure)) unsigned int LoopifyAdvancedPatterns::len_impl(
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        _stack.emplace_back(_Call1{1u});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyAdvancedPatterns::as_guard(
    const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      if (3u < len_impl(_loop_l)) {
        auto _cell = List<unsigned int>::cons(_m.d_a0, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_l = _m.d_a1;
        continue;
      } else {
        _loop_l = _m.d_a1;
        continue;
      }
    }
  }
  return _head;
}

__attribute__((pure)) unsigned int LoopifyAdvancedPatterns::multi_guard(
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<typename List<unsigned int>::Cons &>().d_a0) _s0;
  };

  struct _Call2 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        if (10u < _m.d_a0) {
          _stack.emplace_back(_Call1{_m.d_a0});
          _stack.emplace_back(_Enter{_m.d_a1});
        } else {
          if (0u < _m.d_a0) {
            _stack.emplace_back(_Enter{_m.d_a1});
          } else {
            _stack.emplace_back(_Call2{1u});
            _stack.emplace_back(_Enter{_m.d_a1});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    } else {
      const auto &_f = std::get<_Call2>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyAdvancedPatterns::four_elem(
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype((((std::declval<typename List<unsigned int>::Cons &>().d_a0 +
                std::declval<typename List<unsigned int>::Cons &>().d_a0) +
               std::declval<typename List<unsigned int>::Cons &>().d_a0) +
              std::declval<typename List<unsigned int>::Cons &>().d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        auto &&_sv0 = _m.d_a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv0->v())) {
          _result = 1u;
        } else {
          const auto &_m0 =
              *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
          auto &&_sv1 = _m0.d_a1;
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv1->v())) {
            _result = 2u;
          } else {
            const auto &_m1 =
                *std::get_if<typename List<unsigned int>::Cons>(&_sv1->v());
            auto &&_sv2 = _m1.d_a1;
            if (std::holds_alternative<typename List<unsigned int>::Nil>(
                    _sv2->v())) {
              _result = 3u;
            } else {
              const auto &_m2 =
                  *std::get_if<typename List<unsigned int>::Cons>(&_sv2->v());
              _stack.emplace_back(
                  _Call1{(((_m.d_a0 + _m0.d_a0) + _m1.d_a0) + _m2.d_a0)});
              _stack.emplace_back(_Enter{_m2.d_a1});
            }
          }
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyAdvancedPatterns::nested_pattern(
    const std::shared_ptr<
        List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
        &l) {
  struct _Enter {
    const std::shared_ptr<
        List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
        l;
  };

  struct _Call1 {
    decltype((
        (std::declval<unsigned int &>() + std::declval<unsigned int &>()) +
        std::declval<unsigned int &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<
          List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
          l = _f.l;
      if (std::holds_alternative<typename List<std::pair<
              std::pair<unsigned int, unsigned int>, unsigned int>>::Nil>(
              l->v())) {
        _result = 0u;
      } else {
        const auto &_m = *std::get_if<typename List<std::pair<
            std::pair<unsigned int, unsigned int>, unsigned int>>::Cons>(
            &l->v());
        const std::pair<unsigned int, unsigned int> &p0 = _m.d_a0.first;
        const unsigned int &c = _m.d_a0.second;
        const unsigned int &a = p0.first;
        const unsigned int &b = p0.second;
        _stack.emplace_back(_Call1{((a + b) + c)});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyAdvancedPatterns::guard_accum(
    const unsigned int acc, const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = _loop_acc;
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      if (100u < _m.d_a0) {
        std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
        unsigned int _next_acc = (_loop_acc * 2u);
        _loop_l = std::move(_next_l);
        _loop_acc = std::move(_next_acc);
      } else {
        if (50u < _m.d_a0) {
          std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
          unsigned int _next_acc = (_loop_acc + _m.d_a0);
          _loop_l = std::move(_next_l);
          _loop_acc = std::move(_next_acc);
        } else {
          if (0u < _m.d_a0) {
            std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
            unsigned int _next_acc = (_loop_acc + 1u);
            _loop_l = std::move(_next_l);
            _loop_acc = std::move(_next_acc);
          } else {
            _loop_l = _m.d_a1;
          }
        }
      }
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyAdvancedPatterns::cons_computed(
    const unsigned int n, const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      unsigned int next_n;
      if (0u < _loop_n) {
        next_n = (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
      } else {
        next_n = _loop_n;
      }
      auto _cell = List<unsigned int>::cons(_m.d_a0, nullptr);
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
      unsigned int _next_n = next_n;
      _loop_l = std::move(_next_l);
      _loop_n = std::move(_next_n);
      continue;
    }
  }
  return _head;
}

__attribute__((pure)) unsigned int LoopifyAdvancedPatterns::extract_value(
    const std::shared_ptr<LoopifyAdvancedPatterns::shape> &s) {
  if (std::holds_alternative<typename LoopifyAdvancedPatterns::shape::Circle>(
          s->v())) {
    const auto &_m =
        *std::get_if<typename LoopifyAdvancedPatterns::shape::Circle>(&s->v());
    return _m.d_a0;
  } else if (std::holds_alternative<
                 typename LoopifyAdvancedPatterns::shape::Square>(s->v())) {
    const auto &_m =
        *std::get_if<typename LoopifyAdvancedPatterns::shape::Square>(&s->v());
    return _m.d_a0;
  } else {
    const auto &_m =
        *std::get_if<typename LoopifyAdvancedPatterns::shape::Triangle>(
            &s->v());
    return _m.d_a0;
  }
}

__attribute__((pure)) unsigned int LoopifyAdvancedPatterns::sum_shapes(
    const std::shared_ptr<List<std::shared_ptr<LoopifyAdvancedPatterns::shape>>>
        &l) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyAdvancedPatterns::shape>>>
        l;
  };

  struct _Call1 {
    decltype(extract_value(
        std::declval<typename List<
            std::shared_ptr<LoopifyAdvancedPatterns::shape>>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<
          List<std::shared_ptr<LoopifyAdvancedPatterns::shape>>>
          l = _f.l;
      if (std::holds_alternative<typename List<
              std::shared_ptr<LoopifyAdvancedPatterns::shape>>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m = *std::get_if<typename List<
            std::shared_ptr<LoopifyAdvancedPatterns::shape>>::Cons>(&l->v());
        _stack.emplace_back(_Call1{extract_value(_m.d_a0)});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure))
std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
LoopifyAdvancedPatterns::count_by_shape(
    const std::shared_ptr<List<std::shared_ptr<LoopifyAdvancedPatterns::shape>>>
        &l) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyAdvancedPatterns::shape>>>
        l;
  };

  struct _Call1 {
    const typename List<std::shared_ptr<LoopifyAdvancedPatterns::shape>>::Cons
        _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::pair<unsigned int, unsigned int>, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<
          List<std::shared_ptr<LoopifyAdvancedPatterns::shape>>>
          l = _f.l;
      if (std::holds_alternative<typename List<
              std::shared_ptr<LoopifyAdvancedPatterns::shape>>::Nil>(l->v())) {
        _result = std::make_pair(std::make_pair(0u, 0u), 0u);
      } else {
        const auto &_m = *std::get_if<typename List<
            std::shared_ptr<LoopifyAdvancedPatterns::shape>>::Cons>(&l->v());
        _stack.emplace_back(_Call1{_m});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename List<std::shared_ptr<LoopifyAdvancedPatterns::shape>>::Cons
          _m = _f._s0;
      const std::pair<unsigned int, unsigned int> &p = _result.first;
      const unsigned int &triangles = _result.second;
      const unsigned int &circles = p.first;
      const unsigned int &squares = p.second;
      auto &&_sv = _m.d_a0;
      if (std::holds_alternative<
              typename LoopifyAdvancedPatterns::shape::Circle>(_sv->v())) {
        _result =
            std::make_pair(std::make_pair((circles + 1u), squares), triangles);
      } else if (std::holds_alternative<
                     typename LoopifyAdvancedPatterns::shape::Square>(
                     _sv->v())) {
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

std::shared_ptr<List<unsigned int>> LoopifyAdvancedPatterns::replace_at(
    const unsigned int idx, const unsigned int value,
    const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_idx = idx;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      if (_loop_idx == 0u) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::cons(value, _m.d_a1);
        } else {
          _head = List<unsigned int>::cons(value, _m.d_a1);
        }
        _continue = false;
      } else {
        auto _cell = List<unsigned int>::cons(_m.d_a0, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
        unsigned int _next_idx =
            (((_loop_idx - 1u) > _loop_idx ? 0 : (_loop_idx - 1u)));
        _loop_l = std::move(_next_l);
        _loop_idx = std::move(_next_idx);
        continue;
      }
    }
  }
  return _head;
}
