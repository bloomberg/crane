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
  _stack.reserve(16);
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
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        _stack.emplace_back(_Call1{1u});
        _stack.emplace_back(_Enter{d_a1});
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
  std::shared_ptr<List<unsigned int>> *_write = &_head;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = List<unsigned int>::nil();
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (3u < len_impl(_loop_l)) {
        auto _cell = List<unsigned int>::cons(d_a0, nullptr);
        *_write = _cell;
        _write =
            &std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1;
        _loop_l = d_a1;
        continue;
      } else {
        _loop_l = d_a1;
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
    unsigned int _s0;
  };

  struct _Call2 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
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
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        if (10u < d_a0) {
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{d_a1});
        } else {
          if (0u < d_a0) {
            _stack.emplace_back(_Enter{d_a1});
          } else {
            _stack.emplace_back(_Call2{1u});
            _stack.emplace_back(_Enter{d_a1});
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
    decltype((
        ((std::declval<unsigned int &>() + std::declval<unsigned int &>()) +
         std::declval<unsigned int &>()) +
        std::declval<unsigned int &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
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
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                d_a1->v())) {
          _result = 1u;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(d_a1->v());
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  d_a10->v())) {
            _result = 2u;
          } else {
            const auto &[d_a01, d_a11] =
                std::get<typename List<unsigned int>::Cons>(d_a10->v());
            if (std::holds_alternative<typename List<unsigned int>::Nil>(
                    d_a11->v())) {
              _result = 3u;
            } else {
              const auto &[d_a02, d_a12] =
                  std::get<typename List<unsigned int>::Cons>(d_a11->v());
              _stack.emplace_back(_Call1{(((d_a0 + d_a00) + d_a01) + d_a02)});
              _stack.emplace_back(_Enter{d_a12});
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
  _stack.reserve(16);
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
        const auto &[d_a0, d_a1] = std::get<typename List<std::pair<
            std::pair<unsigned int, unsigned int>, unsigned int>>::Cons>(
            l->v());
        const std::pair<unsigned int, unsigned int> &p0 = d_a0.first;
        const unsigned int &c = d_a0.second;
        const unsigned int &a = p0.first;
        const unsigned int &b = p0.second;
        _stack.emplace_back(_Call1{((a + b) + c)});
        _stack.emplace_back(_Enter{d_a1});
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
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = _loop_acc;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (100u < d_a0) {
        std::shared_ptr<List<unsigned int>> _next_l = d_a1;
        unsigned int _next_acc = (_loop_acc * 2u);
        _loop_l = std::move(_next_l);
        _loop_acc = std::move(_next_acc);
      } else {
        if (50u < d_a0) {
          std::shared_ptr<List<unsigned int>> _next_l = d_a1;
          unsigned int _next_acc = (_loop_acc + d_a0);
          _loop_l = std::move(_next_l);
          _loop_acc = std::move(_next_acc);
        } else {
          if (0u < d_a0) {
            std::shared_ptr<List<unsigned int>> _next_l = d_a1;
            unsigned int _next_acc = (_loop_acc + 1u);
            _loop_l = std::move(_next_l);
            _loop_acc = std::move(_next_acc);
          } else {
            _loop_l = d_a1;
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
  std::shared_ptr<List<unsigned int>> *_write = &_head;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = List<unsigned int>::nil();
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
      auto _cell = List<unsigned int>::cons(d_a0, nullptr);
      *_write = _cell;
      _write =
          &std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1;
      std::shared_ptr<List<unsigned int>> _next_l = d_a1;
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
    const auto &[d_a0] =
        std::get<typename LoopifyAdvancedPatterns::shape::Circle>(s->v());
    return d_a0;
  } else if (std::holds_alternative<
                 typename LoopifyAdvancedPatterns::shape::Square>(s->v())) {
    const auto &[d_a0] =
        std::get<typename LoopifyAdvancedPatterns::shape::Square>(s->v());
    return d_a0;
  } else {
    const auto &[d_a0] =
        std::get<typename LoopifyAdvancedPatterns::shape::Triangle>(s->v());
    return d_a0;
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
        std::declval<std::shared_ptr<LoopifyAdvancedPatterns::shape> &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
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
        const auto &[d_a0, d_a1] = std::get<typename List<
            std::shared_ptr<LoopifyAdvancedPatterns::shape>>::Cons>(l->v());
        _stack.emplace_back(_Call1{extract_value(d_a0)});
        _stack.emplace_back(_Enter{d_a1});
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
    std::shared_ptr<LoopifyAdvancedPatterns::shape> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::pair<unsigned int, unsigned int>, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
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
        const auto &[d_a0, d_a1] = std::get<typename List<
            std::shared_ptr<LoopifyAdvancedPatterns::shape>>::Cons>(l->v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      std::shared_ptr<LoopifyAdvancedPatterns::shape> d_a0 = _f._s0;
      const std::pair<unsigned int, unsigned int> &p = _result.first;
      const unsigned int &triangles = _result.second;
      const unsigned int &circles = p.first;
      const unsigned int &squares = p.second;
      if (std::holds_alternative<
              typename LoopifyAdvancedPatterns::shape::Circle>(d_a0->v())) {
        _result =
            std::make_pair(std::make_pair((circles + 1u), squares), triangles);
      } else if (std::holds_alternative<
                     typename LoopifyAdvancedPatterns::shape::Square>(
                     d_a0->v())) {
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
  std::shared_ptr<List<unsigned int>> *_write = &_head;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_idx = idx;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = List<unsigned int>::nil();
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (_loop_idx == 0u) {
        *_write = List<unsigned int>::cons(value, d_a1);
        break;
      } else {
        auto _cell = List<unsigned int>::cons(d_a0, nullptr);
        *_write = _cell;
        _write =
            &std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1;
        std::shared_ptr<List<unsigned int>> _next_l = d_a1;
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
