#include <loopify_hofs.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
__attribute__((pure)) bool
LoopifyHofs::is_prefix_of(const std::shared_ptr<List<unsigned int>> &l1,
                          const std::shared_ptr<List<unsigned int>> &l2) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1->v())) {
      _result = true;
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2->v())) {
        _result = false;
        _continue = false;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2->v());
        if (d_a0 == d_a00) {
          std::shared_ptr<List<unsigned int>> _next_l2 = d_a10;
          std::shared_ptr<List<unsigned int>> _next_l1 = d_a1;
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
        } else {
          _result = false;
          _continue = false;
        }
      }
    }
  }
  return _result;
}

/// lookup_all key l finds all values associated with key in association list.
std::shared_ptr<List<unsigned int>> LoopifyHofs::lookup_all(
    const unsigned int key,
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename List<std::pair<unsigned int, unsigned int>>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              _loop_l->v());
      const unsigned int &k = d_a0.first;
      const unsigned int &v = d_a0.second;
      if (k == key) {
        auto _cell = List<unsigned int>::cons(v, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
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

/// Helper: get head of list with default.
__attribute__((pure)) unsigned int
LoopifyHofs::head_default(const unsigned int default0,
                          const std::shared_ptr<List<unsigned int>> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
    return default0;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l->v());
    return d_a0;
  }
}

/// subsequences l generates all subsequences of l: 1,2 -> [],[1],[2],[1,2].
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyHofs::subsequences(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = List<std::shared_ptr<List<unsigned int>>>::cons(
            List<unsigned int>::nil(),
            List<std::shared_ptr<List<unsigned int>>>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      unsigned int d_a0 = _f._s0;
      std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> rest = _result;
      std::function<std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>(
          std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>)>
          map_cons_x;
      map_cons_x =
          [&](std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> lsts)
          -> std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> {
        struct _Enter {
          std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> lsts;
        };
        struct _Call1 {
          decltype(List<unsigned int>::cons(
              d_a0, std::declval<std::shared_ptr<List<unsigned int>> &>())) _s0;
        };
        using _Frame = std::variant<_Enter, _Call1>;
        std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
        std::vector<_Frame> _stack;
        _stack.emplace_back(_Enter{lsts});
        while (!_stack.empty()) {
          _Frame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<_Enter>(_frame)) {
            const auto &_f = std::get<_Enter>(_frame);
            std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> lsts =
                _f.lsts;
            if (std::holds_alternative<
                    typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
                    lsts->v())) {
              _result = List<std::shared_ptr<List<unsigned int>>>::nil();
            } else {
              const auto &[d_a00, d_a10] = std::get<
                  typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                  lsts->v());
              _stack.emplace_back(
                  _Call1{List<unsigned int>::cons(d_a0, d_a00)});
              _stack.emplace_back(_Enter{d_a10});
            }
          } else {
            const auto &_f = std::get<_Call1>(_frame);
            _result = List<std::shared_ptr<List<unsigned int>>>::cons(_f._s0,
                                                                      _result);
          }
        }
        return _result;
      };
      _result = rest->app(map_cons_x(rest));
    }
  }
  return _result;
}

/// Helper: pair element with all elements in list.
std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyHofs::pair_with_all(const unsigned int x,
                           const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
            _last->v_mut())
            .d_a1 = List<std::pair<unsigned int, unsigned int>>::nil();
      } else {
        _head = List<std::pair<unsigned int, unsigned int>>::nil();
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto _cell = List<std::pair<unsigned int, unsigned int>>::cons(
          std::make_pair(x, d_a0), nullptr);
      if (_last) {
        std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
            _last->v_mut())
            .d_a1 = _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      _loop_l = d_a1;
      continue;
    }
  }
  return _head;
}

/// cartesian l1 l2 computes cartesian product of two lists.
std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyHofs::cartesian(const std::shared_ptr<List<unsigned int>> &l1,
                       const std::shared_ptr<List<unsigned int>> &l2) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l1;
  };

  struct _Call1 {
    decltype(pair_with_all(
        std::declval<unsigned int &>(),
        std::declval<const std::shared_ptr<List<unsigned int>> &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l1 = _f.l1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l1->v())) {
        _result = List<std::pair<unsigned int, unsigned int>>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l1->v());
        _stack.emplace_back(_Call1{pair_with_all(d_a0, l2)});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = _f._s0->app(_result);
    }
  }
  return _result;
}

/// longest_run l finds the longest consecutive run of equal elements.
/// Matches on recursive result to decide behavior.
std::shared_ptr<List<unsigned int>>
LoopifyHofs::longest_run_fuel(const unsigned int fuel,
                              std::shared_ptr<List<unsigned int>> l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            std::move(_loop_l);
      } else {
        _head = std::move(_loop_l);
      }
      _continue = false;
    } else {
      unsigned int f = _loop_fuel - 1;
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
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l->v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                d_a1->v())) {
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
          } else {
            _head = List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
          }
          _continue = false;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(d_a1->v());
          if (d_a0 == d_a00) {
            auto _cell = List<unsigned int>::cons(d_a0, nullptr);
            if (_last) {
              std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                  _cell;
            } else {
              _head = _cell;
            }
            _last = _cell;
            std::shared_ptr<List<unsigned int>> _next_l =
                List<unsigned int>::cons(d_a00, d_a10);
            unsigned int _next_fuel = f;
            _loop_l = std::move(_next_l);
            _loop_fuel = std::move(_next_fuel);
            continue;
          } else {
            std::shared_ptr<List<unsigned int>> rec_result =
                longest_run_fuel(f, List<unsigned int>::cons(d_a00, d_a10));
            if (std::holds_alternative<typename List<unsigned int>::Nil>(
                    rec_result->v())) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 =
                    List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
              } else {
                _head =
                    List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
              }
              _continue = false;
            } else {
              const auto &[d_a01, d_a11] =
                  std::get<typename List<unsigned int>::Cons>(rec_result->v());
              if (d_a0 == d_a01) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = std::move(rec_result);
                } else {
                  _head = std::move(rec_result);
                }
                _continue = false;
              } else {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = std::move(rec_result);
                } else {
                  _head = std::move(rec_result);
                }
                _continue = false;
              }
            }
          }
        }
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyHofs::longest_run(const std::shared_ptr<List<unsigned int>> &l) {
  return longest_run_fuel(l->length(), l);
}

/// power_set l generates all subsets.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyHofs::power_set(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = List<std::shared_ptr<List<unsigned int>>>::cons(
            List<unsigned int>::nil(),
            List<std::shared_ptr<List<unsigned int>>>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      unsigned int d_a0 = _f._s0;
      std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> sub = _result;
      std::function<std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>(
          std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>)>
          map_cons_x;
      map_cons_x =
          [&](std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> lsts)
          -> std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> {
        struct _Enter {
          std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> lsts;
        };
        struct _Call1 {
          decltype(List<unsigned int>::cons(
              d_a0, std::declval<std::shared_ptr<List<unsigned int>> &>())) _s0;
        };
        using _Frame = std::variant<_Enter, _Call1>;
        std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
        std::vector<_Frame> _stack;
        _stack.emplace_back(_Enter{lsts});
        while (!_stack.empty()) {
          _Frame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<_Enter>(_frame)) {
            const auto &_f = std::get<_Enter>(_frame);
            std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> lsts =
                _f.lsts;
            if (std::holds_alternative<
                    typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
                    lsts->v())) {
              _result = List<std::shared_ptr<List<unsigned int>>>::nil();
            } else {
              const auto &[d_a00, d_a10] = std::get<
                  typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                  lsts->v());
              _stack.emplace_back(
                  _Call1{List<unsigned int>::cons(d_a0, d_a00)});
              _stack.emplace_back(_Enter{d_a10});
            }
          } else {
            const auto &_f = std::get<_Call1>(_frame);
            _result = List<std::shared_ptr<List<unsigned int>>>::cons(_f._s0,
                                                                      _result);
          }
        }
        return _result;
      };
      _result = sub->app(map_cons_x(sub));
    }
  }
  return _result;
}
