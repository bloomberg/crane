#include <loopify_pairs.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Consolidated UNIQUE pair/tuple operations.
/// unzip l splits list of nat pairs into pair of lists.
__attribute__((pure))
std::pair<std::shared_ptr<LoopifyPairs::list<unsigned int>>,
          std::shared_ptr<LoopifyPairs::list<unsigned int>>>
LoopifyPairs::unzip(
    const std::shared_ptr<
        LoopifyPairs::list<std::pair<unsigned int, unsigned int>>> &l) {
  struct _Enter {
    const std::shared_ptr<
        LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>
        l;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<LoopifyPairs::list<unsigned int>>,
            std::shared_ptr<LoopifyPairs::list<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<
          LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>
          l = _f.l;
      if (std::holds_alternative<typename LoopifyPairs::list<
              std::pair<unsigned int, unsigned int>>::Nil>(l->v())) {
        _result = std::make_pair(list<unsigned int>::nil(),
                                 list<unsigned int>::nil());
      } else {
        const auto &_m = *std::get_if<typename LoopifyPairs::list<
            std::pair<unsigned int, unsigned int>>::Cons>(&l->v());
        const unsigned int &x = _m.d_a0.first;
        const unsigned int &y = _m.d_a0.second;
        _stack.emplace_back(_Call1{y, x});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      unsigned int y = _f._s0;
      unsigned int x = _f._s1;
      const std::shared_ptr<LoopifyPairs::list<unsigned int>> &xs =
          _result.first;
      const std::shared_ptr<LoopifyPairs::list<unsigned int>> &ys =
          _result.second;
      _result = std::make_pair(list<unsigned int>::cons(x, xs),
                               list<unsigned int>::cons(y, ys));
    }
  }
  return _result;
}

/// partition3 pivot l three-way partition around pivot.
__attribute__((pure))
std::pair<std::shared_ptr<LoopifyPairs::list<unsigned int>>,
          std::pair<std::shared_ptr<LoopifyPairs::list<unsigned int>>,
                    std::shared_ptr<LoopifyPairs::list<unsigned int>>>>
LoopifyPairs::partition3(
    const unsigned int pivot,
    const std::shared_ptr<LoopifyPairs::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyPairs::list<unsigned int>> l;
  };

  struct _Call1 {
    const unsigned int _s0;
    const typename LoopifyPairs::list<unsigned int>::Cons _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<LoopifyPairs::list<unsigned int>>,
            std::pair<std::shared_ptr<LoopifyPairs::list<unsigned int>>,
                      std::shared_ptr<LoopifyPairs::list<unsigned int>>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<LoopifyPairs::list<unsigned int>> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyPairs::list<unsigned int>::Nil>(l->v())) {
        _result = std::make_pair(list<unsigned int>::nil(),
                                 std::make_pair(list<unsigned int>::nil(),
                                                list<unsigned int>::nil()));
      } else {
        const auto &_m =
            *std::get_if<typename LoopifyPairs::list<unsigned int>::Cons>(
                &l->v());
        _stack.emplace_back(_Call1{pivot, _m});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const unsigned int pivot = _f._s0;
      const typename LoopifyPairs::list<unsigned int>::Cons _m = _f._s1;
      const std::shared_ptr<LoopifyPairs::list<unsigned int>> &lt =
          _result.first;
      const std::pair<std::shared_ptr<LoopifyPairs::list<unsigned int>>,
                      std::shared_ptr<LoopifyPairs::list<unsigned int>>> &p =
          _result.second;
      const std::shared_ptr<LoopifyPairs::list<unsigned int>> &eq = p.first;
      const std::shared_ptr<LoopifyPairs::list<unsigned int>> &gt = p.second;
      if (_m.d_a0 < pivot) {
        _result = std::make_pair(list<unsigned int>::cons(_m.d_a0, lt),
                                 std::make_pair(eq, gt));
      } else {
        if (_m.d_a0 == pivot) {
          _result = std::make_pair(
              lt, std::make_pair(list<unsigned int>::cons(_m.d_a0, eq), gt));
        } else {
          _result = std::make_pair(
              lt, std::make_pair(eq, list<unsigned int>::cons(_m.d_a0, gt)));
        }
      }
    }
  }
  return _result;
}

/// min_max l finds both min and max in one pass.
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyPairs::min_max(
    const std::shared_ptr<LoopifyPairs::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyPairs::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyPairs::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<LoopifyPairs::list<unsigned int>> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyPairs::list<unsigned int>::Nil>(l->v())) {
        _result = std::make_pair(0u, 0u);
      } else {
        const auto &_m =
            *std::get_if<typename LoopifyPairs::list<unsigned int>::Cons>(
                &l->v());
        auto &&_sv = _m.d_a1;
        if (std::holds_alternative<
                typename LoopifyPairs::list<unsigned int>::Nil>(_sv->v())) {
          _result = std::make_pair(_m.d_a0, _m.d_a0);
        } else {
          _stack.emplace_back(_Call1{_m});
          _stack.emplace_back(_Enter{_m.d_a1});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename LoopifyPairs::list<unsigned int>::Cons _m = _f._s0;
      const unsigned int &mn = _result.first;
      const unsigned int &mx = _result.second;
      _result = std::make_pair(
          [&]() -> unsigned int {
            if (_m.d_a0 <= mn) {
              return _m.d_a0;
            } else {
              return mn;
            }
          }(),
          [&]() -> unsigned int {
            if (mx <= _m.d_a0) {
              return _m.d_a0;
            } else {
              return mx;
            }
          }());
    }
  }
  return _result;
}

/// sum_and_count computes both in one pass.
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyPairs::sum_and_count(
    const std::shared_ptr<LoopifyPairs::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyPairs::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyPairs::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<LoopifyPairs::list<unsigned int>> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyPairs::list<unsigned int>::Nil>(l->v())) {
        _result = std::make_pair(0u, 0u);
      } else {
        const auto &_m =
            *std::get_if<typename LoopifyPairs::list<unsigned int>::Cons>(
                &l->v());
        _stack.emplace_back(_Call1{_m});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename LoopifyPairs::list<unsigned int>::Cons _m = _f._s0;
      const unsigned int &s = _result.first;
      const unsigned int &c = _result.second;
      _result = std::make_pair((_m.d_a0 + s), (c + 1));
    }
  }
  return _result;
}

/// sum_prod_count triple accumulator.
__attribute__((pure))
std::pair<unsigned int, std::pair<unsigned int, unsigned int>>
LoopifyPairs::sum_prod_count(
    const std::shared_ptr<LoopifyPairs::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyPairs::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyPairs::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, std::pair<unsigned int, unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<LoopifyPairs::list<unsigned int>> l = _f.l;
      if (std::holds_alternative<
              typename LoopifyPairs::list<unsigned int>::Nil>(l->v())) {
        _result = std::make_pair(0u, std::make_pair(1u, 0u));
      } else {
        const auto &_m =
            *std::get_if<typename LoopifyPairs::list<unsigned int>::Cons>(
                &l->v());
        _stack.emplace_back(_Call1{_m});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename LoopifyPairs::list<unsigned int>::Cons _m = _f._s0;
      const unsigned int &s = _result.first;
      const std::pair<unsigned int, unsigned int> &p0 = _result.second;
      const unsigned int &p = p0.first;
      const unsigned int &c = p0.second;
      _result =
          std::make_pair((_m.d_a0 + s), std::make_pair((_m.d_a0 * p), (c + 1)));
    }
  }
  return _result;
}

/// lookup_all key l finds all values associated with key.
std::shared_ptr<LoopifyPairs::list<unsigned int>> LoopifyPairs::lookup_all(
    const unsigned int key,
    const std::shared_ptr<
        LoopifyPairs::list<std::pair<unsigned int, unsigned int>>> &l) {
  std::shared_ptr<LoopifyPairs::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyPairs::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>
      _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename LoopifyPairs::list<
            std::pair<unsigned int, unsigned int>>::Nil>(_loop_l->v())) {
      if (_last) {
        std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            list<unsigned int>::nil();
      } else {
        _head = list<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &_m = *std::get_if<typename LoopifyPairs::list<
          std::pair<unsigned int, unsigned int>>::Cons>(&_loop_l->v());
      const unsigned int &k = _m.d_a0.first;
      const unsigned int &v = _m.d_a0.second;
      if (k == key) {
        auto _cell = list<unsigned int>::cons(v, nullptr);
        if (_last) {
          std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
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

/// swap_pairs l swaps elements in each pair.
std::shared_ptr<LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>
LoopifyPairs::swap_pairs(
    const std::shared_ptr<
        LoopifyPairs::list<std::pair<unsigned int, unsigned int>>> &l) {
  std::shared_ptr<LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>
      _head{};
  std::shared_ptr<LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>
      _last{};
  std::shared_ptr<LoopifyPairs::list<std::pair<unsigned int, unsigned int>>>
      _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename LoopifyPairs::list<
            std::pair<unsigned int, unsigned int>>::Nil>(_loop_l->v())) {
      if (_last) {
        std::get<typename list<std::pair<unsigned int, unsigned int>>::Cons>(
            _last->v_mut())
            .d_a1 = list<std::pair<unsigned int, unsigned int>>::nil();
      } else {
        _head = list<std::pair<unsigned int, unsigned int>>::nil();
      }
      _continue = false;
    } else {
      const auto &_m = *std::get_if<typename LoopifyPairs::list<
          std::pair<unsigned int, unsigned int>>::Cons>(&_loop_l->v());
      const unsigned int &a = _m.d_a0.first;
      const unsigned int &b = _m.d_a0.second;
      auto _cell = list<std::pair<unsigned int, unsigned int>>::cons(
          std::make_pair(b, a), nullptr);
      if (_last) {
        std::get<typename list<std::pair<unsigned int, unsigned int>>::Cons>(
            _last->v_mut())
            .d_a1 = _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      _loop_l = _m.d_a1;
      continue;
    }
  }
  return _head;
}
