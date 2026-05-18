#include "loopify_pairs.h"

/// Consolidated UNIQUE pair/tuple operations.
/// unzip l splits list of nat pairs into pair of lists.
std::pair<LoopifyPairs::list<uint64_t>, LoopifyPairs::list<uint64_t>>
LoopifyPairs::unzip(
    const LoopifyPairs::list<std::pair<uint64_t, uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> *l;
  };

  /// _Cont_x: saves [x, y], resumes after recursive call, then processes rest.
  struct _Cont_x {
    uint64_t x;
    uint64_t y;
  };

  using _Frame = std::variant<_Enter, _Cont_x>;
  std::pair<LoopifyPairs::list<uint64_t>, LoopifyPairs::list<uint64_t>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified unzip: _Enter -> _Cont_x.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Nil>(
              l.v())) {
        _result = std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<
            typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Cons>(
            l.v());
        const uint64_t &x = a0.first;
        const uint64_t &y = a0.second;
        _stack.emplace_back(_Cont_x{x, y});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_x>(_frame));
      uint64_t x = _f.x;
      uint64_t y = _f.y;
      const LoopifyPairs::list<uint64_t> &xs = _result.first;
      const LoopifyPairs::list<uint64_t> &ys = _result.second;
      _result = std::make_pair(list<uint64_t>::cons(x, xs),
                               list<uint64_t>::cons(y, ys));
    }
  }
  return _result;
}

/// partition3 pivot l three-way partition around pivot.
std::pair<LoopifyPairs::list<uint64_t>,
          std::pair<LoopifyPairs::list<uint64_t>, LoopifyPairs::list<uint64_t>>>
LoopifyPairs::partition3(
    uint64_t pivot,
    const LoopifyPairs::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyPairs::list<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0, pivot], resumes after recursive call, then
  /// processes rest.
  struct _Cont_Cons {
    uint64_t a0;
    uint64_t pivot;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<
      LoopifyPairs::list<uint64_t>,
      std::pair<LoopifyPairs::list<uint64_t>, LoopifyPairs::list<uint64_t>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified partition3: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPairs::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyPairs::list<uint64_t>::Nil>(
              l.v())) {
        _result = std::make_pair(
            list<uint64_t>::nil(),
            std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil()));
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPairs::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0, pivot});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      uint64_t pivot = _f.pivot;
      const LoopifyPairs::list<uint64_t> &lt = _result.first;
      const std::pair<LoopifyPairs::list<uint64_t>,
                      LoopifyPairs::list<uint64_t>> &p = _result.second;
      const LoopifyPairs::list<uint64_t> &eq = p.first;
      const LoopifyPairs::list<uint64_t> &gt = p.second;
      if (a0 < pivot) {
        _result = std::make_pair(list<uint64_t>::cons(a0, lt),
                                 std::make_pair(eq, gt));
      } else {
        if (a0 == pivot) {
          _result = std::make_pair(
              lt, std::make_pair(list<uint64_t>::cons(a0, eq), gt));
        } else {
          _result = std::make_pair(
              lt, std::make_pair(eq, list<uint64_t>::cons(a0, gt)));
        }
      }
    }
  }
  return _result;
}

/// min_max l finds both min and max in one pass.
std::pair<uint64_t, uint64_t> LoopifyPairs::min_max(
    const LoopifyPairs::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyPairs::list<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<uint64_t, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified min_max: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPairs::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyPairs::list<uint64_t>::Nil>(
              l.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPairs::list<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename LoopifyPairs::list<uint64_t>::Nil>(
                _sv.v())) {
          _result = std::make_pair(a0, a0);
        } else {
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      const uint64_t &mn = _result.first;
      const uint64_t &mx = _result.second;
      _result = std::make_pair((a0 <= mn ? a0 : mn), (mx <= a0 ? a0 : mx));
    }
  }
  return _result;
}

/// sum_and_count computes both in one pass.
std::pair<uint64_t, uint64_t> LoopifyPairs::sum_and_count(
    const LoopifyPairs::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyPairs::list<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<uint64_t, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_and_count: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPairs::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyPairs::list<uint64_t>::Nil>(
              l.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPairs::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      const uint64_t &s = _result.first;
      const uint64_t &c = _result.second;
      _result = std::make_pair((a0 + s), (c + 1));
    }
  }
  return _result;
}

/// sum_prod_count triple accumulator.
std::pair<uint64_t, std::pair<uint64_t, uint64_t>> LoopifyPairs::sum_prod_count(
    const LoopifyPairs::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyPairs::list<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<uint64_t, std::pair<uint64_t, uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_prod_count: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyPairs::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyPairs::list<uint64_t>::Nil>(
              l.v())) {
        _result = std::make_pair(UINT64_C(0),
                                 std::make_pair(UINT64_C(1), UINT64_C(0)));
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPairs::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      const uint64_t &s = _result.first;
      const std::pair<uint64_t, uint64_t> &p0 = _result.second;
      const uint64_t &p = p0.first;
      const uint64_t &c = p0.second;
      _result = std::make_pair((a0 + s), std::make_pair((a0 * p), (c + 1)));
    }
  }
  return _result;
}

/// lookup_all key l finds all values associated with key.
LoopifyPairs::list<uint64_t> LoopifyPairs::lookup_all(
    uint64_t key, const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> &l) {
  std::unique_ptr<LoopifyPairs::list<uint64_t>> _head{};
  std::unique_ptr<LoopifyPairs::list<uint64_t>> *_write = &_head;
  const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Nil>(
            _loop_l->v())) {
      *_write =
          std::make_unique<LoopifyPairs::list<uint64_t>>(list<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Cons>(
          _loop_l->v());
      const uint64_t &k = a0.first;
      const uint64_t &v = a0.second;
      if (k == key) {
        auto _cell = std::make_unique<LoopifyPairs::list<uint64_t>>(
            typename list<uint64_t>::Cons(v, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename list<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = a1.get();
        continue;
      } else {
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// swap_pairs l swaps elements in each pair.
LoopifyPairs::list<std::pair<uint64_t, uint64_t>> LoopifyPairs::swap_pairs(
    const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> &l) {
  std::unique_ptr<LoopifyPairs::list<std::pair<uint64_t, uint64_t>>> _head{};
  std::unique_ptr<LoopifyPairs::list<std::pair<uint64_t, uint64_t>>> *_write =
      &_head;
  const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Nil>(
            _loop_l->v())) {
      *_write =
          std::make_unique<LoopifyPairs::list<std::pair<uint64_t, uint64_t>>>(
              list<std::pair<uint64_t, uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Cons>(
          _loop_l->v());
      const uint64_t &a = a0.first;
      const uint64_t &b = a0.second;
      auto _cell =
          std::make_unique<LoopifyPairs::list<std::pair<uint64_t, uint64_t>>>(
              typename list<std::pair<uint64_t, uint64_t>>::Cons(
                  std::make_pair(b, a), nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename list<std::pair<uint64_t, uint64_t>>::Cons>(
                    (*_write)->v_mut())
                    .l;
      _loop_l = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}
