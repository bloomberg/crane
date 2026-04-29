#include <loopify_pairs.h>

/// Consolidated UNIQUE pair/tuple operations.
/// unzip l splits list of nat pairs into pair of lists.
__attribute__((pure))
std::pair<LoopifyPairs::list<unsigned int>, LoopifyPairs::list<unsigned int>>
LoopifyPairs::unzip(
    const LoopifyPairs::list<std::pair<unsigned int, unsigned int>> &l) {
  struct _Enter {
    const LoopifyPairs::list<std::pair<unsigned int, unsigned int>> *l;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<LoopifyPairs::list<unsigned int>, LoopifyPairs::list<unsigned int>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPairs::list<std::pair<unsigned int, unsigned int>> &l =
          *(_f.l);
      if (std::holds_alternative<typename LoopifyPairs::list<
              std::pair<unsigned int, unsigned int>>::Nil>(l.v())) {
        _result = std::make_pair(list<unsigned int>::nil(),
                                 list<unsigned int>::nil());
      } else {
        const auto &[d_a0, d_a1] = std::get<typename LoopifyPairs::list<
            std::pair<unsigned int, unsigned int>>::Cons>(l.v());
        const unsigned int &x = d_a0.first;
        const unsigned int &y = d_a0.second;
        _stack.emplace_back(_Call1{x, y});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int x = std::move(_f._s0);
      unsigned int y = std::move(_f._s1);
      const LoopifyPairs::list<unsigned int> &xs = _result.first;
      const LoopifyPairs::list<unsigned int> &ys = _result.second;
      _result = std::make_pair(list<unsigned int>::cons(x, xs),
                               list<unsigned int>::cons(y, ys));
    }
  }
  return _result;
}

/// partition3 pivot l three-way partition around pivot.
__attribute__((pure)) std::pair<LoopifyPairs::list<unsigned int>,
                                std::pair<LoopifyPairs::list<unsigned int>,
                                          LoopifyPairs::list<unsigned int>>>
LoopifyPairs::partition3(const unsigned int &pivot,
                         const LoopifyPairs::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyPairs::list<unsigned int> *l;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<LoopifyPairs::list<unsigned int>,
            std::pair<LoopifyPairs::list<unsigned int>,
                      LoopifyPairs::list<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPairs::list<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<
              typename LoopifyPairs::list<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(list<unsigned int>::nil(),
                                 std::make_pair(list<unsigned int>::nil(),
                                                list<unsigned int>::nil()));
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyPairs::list<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0, pivot});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
      const unsigned int &pivot = _f._s1;
      const LoopifyPairs::list<unsigned int> &lt = _result.first;
      const std::pair<LoopifyPairs::list<unsigned int>,
                      LoopifyPairs::list<unsigned int>> &p = _result.second;
      const LoopifyPairs::list<unsigned int> &eq = p.first;
      const LoopifyPairs::list<unsigned int> &gt = p.second;
      if (d_a0 < pivot) {
        _result = std::make_pair(list<unsigned int>::cons(d_a0, lt),
                                 std::make_pair(eq, gt));
      } else {
        if (d_a0 == pivot) {
          _result = std::make_pair(
              lt, std::make_pair(list<unsigned int>::cons(d_a0, eq), gt));
        } else {
          _result = std::make_pair(
              lt, std::make_pair(eq, list<unsigned int>::cons(d_a0, gt)));
        }
      }
    }
  }
  return _result;
}

/// min_max l finds both min and max in one pass.
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyPairs::min_max(const LoopifyPairs::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyPairs::list<unsigned int> *l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPairs::list<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<
              typename LoopifyPairs::list<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(0u, 0u);
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyPairs::list<unsigned int>::Cons>(l.v());
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<
                typename LoopifyPairs::list<unsigned int>::Nil>(_sv.v())) {
          _result = std::make_pair(d_a0, d_a0);
        } else {
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
      const unsigned int &mn = _result.first;
      const unsigned int &mx = _result.second;
      _result =
          std::make_pair((d_a0 <= mn ? d_a0 : mn), (mx <= d_a0 ? d_a0 : mx));
    }
  }
  return _result;
}

/// sum_and_count computes both in one pass.
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyPairs::sum_and_count(const LoopifyPairs::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyPairs::list<unsigned int> *l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPairs::list<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<
              typename LoopifyPairs::list<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(0u, 0u);
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyPairs::list<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
      const unsigned int &s = _result.first;
      const unsigned int &c = _result.second;
      _result = std::make_pair((d_a0 + s), (c + 1));
    }
  }
  return _result;
}

/// sum_prod_count triple accumulator.
__attribute__((pure))
std::pair<unsigned int, std::pair<unsigned int, unsigned int>>
LoopifyPairs::sum_prod_count(const LoopifyPairs::list<unsigned int> &l) {
  struct _Enter {
    const LoopifyPairs::list<unsigned int> *l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, std::pair<unsigned int, unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPairs::list<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<
              typename LoopifyPairs::list<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(0u, std::make_pair(1u, 0u));
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename LoopifyPairs::list<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
      const unsigned int &s = _result.first;
      const std::pair<unsigned int, unsigned int> &p0 = _result.second;
      const unsigned int &p = p0.first;
      const unsigned int &c = p0.second;
      _result = std::make_pair((d_a0 + s), std::make_pair((d_a0 * p), (c + 1)));
    }
  }
  return _result;
}

/// lookup_all key l finds all values associated with key.
__attribute__((pure)) LoopifyPairs::list<unsigned int> LoopifyPairs::lookup_all(
    const unsigned int &key,
    const LoopifyPairs::list<std::pair<unsigned int, unsigned int>> &l) {
  std::unique_ptr<LoopifyPairs::list<unsigned int>> _head{};
  std::unique_ptr<LoopifyPairs::list<unsigned int>> *_write = &_head;
  const LoopifyPairs::list<std::pair<unsigned int, unsigned int>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyPairs::list<
            std::pair<unsigned int, unsigned int>>::Nil>(_loop_l->v())) {
      *(_write) = std::make_unique<LoopifyPairs::list<unsigned int>>(
          list<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename LoopifyPairs::list<
          std::pair<unsigned int, unsigned int>>::Cons>(_loop_l->v());
      const unsigned int &k = d_a0.first;
      const unsigned int &v = d_a0.second;
      if (k == key) {
        auto _cell = std::make_unique<LoopifyPairs::list<unsigned int>>(
            typename list<unsigned int>::Cons(v, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename list<unsigned int>::Cons>((*_write)->v_mut())
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

/// swap_pairs l swaps elements in each pair.
__attribute__((pure)) LoopifyPairs::list<std::pair<unsigned int, unsigned int>>
LoopifyPairs::swap_pairs(
    const LoopifyPairs::list<std::pair<unsigned int, unsigned int>> &l) {
  std::unique_ptr<LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>
      _head{};
  std::unique_ptr<LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>
      *_write = &_head;
  const LoopifyPairs::list<std::pair<unsigned int, unsigned int>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename LoopifyPairs::list<
            std::pair<unsigned int, unsigned int>>::Nil>(_loop_l->v())) {
      *(_write) = std::make_unique<
          LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>(
          list<std::pair<unsigned int, unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename LoopifyPairs::list<
          std::pair<unsigned int, unsigned int>>::Cons>(_loop_l->v());
      const unsigned int &a = d_a0.first;
      const unsigned int &b = d_a0.second;
      auto _cell = std::make_unique<
          LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>(
          typename list<std::pair<unsigned int, unsigned int>>::Cons(
              std::make_pair(b, a), nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename list<std::pair<unsigned int, unsigned int>>::Cons>(
               (*_write)->v_mut())
               .d_a1;
      _loop_l = d_a1.get();
      continue;
    }
  }
  return std::move(*(_head));
}
