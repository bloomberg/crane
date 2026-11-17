#include "loopify_pairs.h"

/// Consolidated UNIQUE pair/tuple operations.
/// unzip l splits list of nat pairs into pair of lists.
std::pair<LoopifyPairs::list<uint64_t>, LoopifyPairs::list<uint64_t>>
LoopifyPairs::unzip(const LoopifyPairs::list<std::pair<uint64_t,
                                                       uint64_t>> &l) {
  // Explicit stack replaces the non-tail recursion of unzip: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> *l;
  };

  struct _after_unzip_in_pair {
    uint64_t x;
    uint64_t y;
  };

  using _frame = std::variant<_call, _after_unzip_in_pair>;
  std::pair<LoopifyPairs::list<uint64_t>,
            LoopifyPairs::list<uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Nil>(
              l.v())) {
        _result = std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<
            typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Cons>(
            l.v());
        const auto &[x, y] = a0;
        _stack.emplace_back(_after_unzip_in_pair{x, y});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_unzip_in_pair>(_popped));
      uint64_t x = _f.x;
      uint64_t y = _f.y;
      auto [xs, ys] = std::move(_result);
      _result = std::make_pair(list<uint64_t>::cons(x, std::move(xs)),
                               list<uint64_t>::cons(y, std::move(ys)));
    }
  }
  return _result;
}

/// partition3 pivot l three-way partition around pivot.
std::pair<LoopifyPairs::list<uint64_t>,
          std::pair<LoopifyPairs::list<uint64_t>, LoopifyPairs::list<uint64_t>>>
LoopifyPairs::partition3(uint64_t pivot,
                         const LoopifyPairs::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of partition3: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyPairs::list<uint64_t> *l;
  };

  struct _after_partition3_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_partition3_in_Cons>;
  std::pair<
      LoopifyPairs::list<uint64_t>,
      std::pair<LoopifyPairs::list<uint64_t>,
                LoopifyPairs::list<uint64_t>>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const LoopifyPairs::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyPairs::list<uint64_t>::Nil>(
              l.v())) {
        _result = std::make_pair(
            list<uint64_t>::nil(),
            std::make_pair(list<uint64_t>::nil(), list<uint64_t>::nil()));
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPairs::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_partition3_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_partition3_in_Cons>(_popped));
      uint64_t a0 = _f.a0;
      auto [lt, p] = std::move(_result);
      auto [eq, gt] = std::move(p);
      if (a0 < pivot) {
        _result = std::make_pair(list<uint64_t>::cons(a0, std::move(lt)),
                                 std::make_pair(std::move(eq), std::move(gt)));
      } else {
        if (a0 == pivot) {
          _result = std::make_pair(
              std::move(lt),
              std::make_pair(list<uint64_t>::cons(a0, std::move(eq)),
                             std::move(gt)));
        } else {
          _result = std::make_pair(
              std::move(lt),
              std::make_pair(std::move(eq),
                             list<uint64_t>::cons(a0, std::move(gt))));
        }
      }
    }
  }
  return _result;
}

/// min_max l finds both min and max in one pass.
std::pair<uint64_t, uint64_t>
LoopifyPairs::min_max(const LoopifyPairs::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of min_max: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyPairs::list<uint64_t> *l;
  };

  struct _after_min_max_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_min_max_in_Cons>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
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
          _stack.emplace_back(_after_min_max_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_min_max_in_Cons>(_popped));
      uint64_t a0 = _f.a0;
      std::pair<uint64_t, uint64_t> _tmp1 = std::move(_result);
      const auto &[mn, mx] = _tmp1;
      _result = std::make_pair((a0 <= mn ? a0 : mn), (mx <= a0 ? a0 : mx));
    }
  }
  return _result;
}

/// sum_and_count computes both in one pass.
std::pair<uint64_t, uint64_t>
LoopifyPairs::sum_and_count(const LoopifyPairs::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of sum_and_count: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyPairs::list<uint64_t> *l;
  };

  struct _after_sum_and_count_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sum_and_count_in_Cons>;
  std::pair<uint64_t, uint64_t> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const LoopifyPairs::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyPairs::list<uint64_t>::Nil>(
              l.v())) {
        _result = std::make_pair(UINT64_C(0), UINT64_C(0));
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPairs::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_sum_and_count_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_and_count_in_Cons>(_popped));
      uint64_t a0 = _f.a0;
      std::pair<uint64_t, uint64_t> _tmp1 = std::move(_result);
      const auto &[s, c] = _tmp1;
      _result = std::make_pair((a0 + s), (c + 1));
    }
  }
  return _result;
}

/// sum_prod_count triple accumulator.
std::pair<uint64_t, std::pair<uint64_t, uint64_t>>
LoopifyPairs::sum_prod_count(const LoopifyPairs::list<uint64_t> &l) {
  // Explicit stack replaces the non-tail recursion of sum_prod_count: _call
  // frames are pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyPairs::list<uint64_t> *l;
  };

  struct _after_sum_prod_count_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sum_prod_count_in_Cons>;
  std::pair<uint64_t, std::pair<uint64_t, uint64_t>> _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const LoopifyPairs::list<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename LoopifyPairs::list<uint64_t>::Nil>(
              l.v())) {
        _result = std::make_pair(UINT64_C(0),
                                 std::make_pair(UINT64_C(1), UINT64_C(0)));
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyPairs::list<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_after_sum_prod_count_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum_prod_count_in_Cons>(_popped));
      uint64_t a0 = _f.a0;
      std::pair<uint64_t, std::pair<uint64_t, uint64_t>> _tmp1 =
          std::move(_result);
      const auto &[s, p0] = _tmp1;
      const auto &[p, c] = p0;
      _result = std::make_pair((a0 + s), std::make_pair((a0 * p), (c + 1)));
    }
  }
  return _result;
}

/// lookup_all key l finds all values associated with key.
LoopifyPairs::list<uint64_t> LoopifyPairs::lookup_all(
    uint64_t key, const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyPairs::list<uint64_t>> _root{};
  std::shared_ptr<LoopifyPairs::list<uint64_t>> *_write = nullptr;
  const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Nil>(
            _loop_l->v())) {
      auto _value = list<uint64_t>::nil();
      (_write ? *(*_write = std::make_shared<LoopifyPairs::list<uint64_t>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Cons>(
          _loop_l->v());
      const auto &[k, v] = a0;
      if (k == key) {
        auto _cell = typename LoopifyPairs::list<uint64_t>::Cons(v, nullptr);
        LoopifyPairs::list<uint64_t> &_node = (
            _write ? *(*_write = std::make_shared<LoopifyPairs::list<uint64_t>>(
                           std::move(_cell)))
                   : _root.emplace(std::move(_cell)));
        _write =
            &std::get<typename LoopifyPairs::list<uint64_t>::Cons>(
                _node.v_mut())
                .l;
        _loop_l = crane_raw(a1);
        continue;
      } else {
        _loop_l = crane_raw(a1);
        continue;
      }
    }
  }
  return std::move(*_root);
}

/// swap_pairs l swaps elements in each pair.
LoopifyPairs::list<std::pair<uint64_t, uint64_t>> LoopifyPairs::swap_pairs(
    const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> &l) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyPairs::list<std::pair<uint64_t, uint64_t>>> _root{};
  std::shared_ptr<LoopifyPairs::list<std::pair<uint64_t, uint64_t>>> *_write =
      nullptr;
  const LoopifyPairs::list<std::pair<uint64_t, uint64_t>> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Nil>(
            _loop_l->v())) {
      auto _value = list<std::pair<uint64_t, uint64_t>>::nil();
      (_write ? *(*_write = std::make_shared<
                      LoopifyPairs::list<std::pair<uint64_t, uint64_t>>>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] = std::get<
          typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Cons>(
          _loop_l->v());
      const auto &[a, b] = a0;
      auto _cell =
          typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Cons(
              std::make_pair(b, a), nullptr);
      LoopifyPairs::list<std::pair<uint64_t, uint64_t>> &_node =
          (_write ? *(*_write = std::make_shared<
                          LoopifyPairs::list<std::pair<uint64_t, uint64_t>>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<
              typename LoopifyPairs::list<std::pair<uint64_t, uint64_t>>::Cons>(
              _node.v_mut())
              .l;
      _loop_l = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}
