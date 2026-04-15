#include <loopify_combinatorics.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

/// Consolidated combinatorial algorithms.
/// remove x l removes first occurrence of x from list.
std::shared_ptr<List<unsigned int>>
LoopifyCombinatorics::remove(const unsigned int x,
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
      if (x == _m.d_a0) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _m.d_a1;
        } else {
          _head = _m.d_a1;
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
        _loop_l = _m.d_a1;
        continue;
      }
    }
  }
  return _head;
}

/// Helper: prepend x to each list in lsts.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyCombinatorics::map_cons(
    const unsigned int x,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &lsts) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_lsts = lsts;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
            _loop_lsts->v())) {
      if (_last) {
        std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
            _last->v_mut())
            .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
      } else {
        _head = List<std::shared_ptr<List<unsigned int>>>::nil();
      }
      _continue = false;
    } else {
      const auto &_m = *std::get_if<
          typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
          &_loop_lsts->v());
      auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
          List<unsigned int>::cons(x, _m.d_a0), nullptr);
      if (_last) {
        std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
            _last->v_mut())
            .d_a1 = _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      _loop_lsts = _m.d_a1;
      continue;
    }
  }
  return _head;
}

/// perms_choices_fuel fuel choices orig generates permutations by iterating
/// over choices.  Single self-recursive function that handles both the choice
/// iteration and the recursive subproblem, enabling full loopification.
/// The match on remaining is hoisted out of the let-binding so that all
/// recursive calls appear at the top level of each branch.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyCombinatorics::perms_choices_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &choices,
    const std::shared_ptr<List<unsigned int>> &orig) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> orig;
    const std::shared_ptr<List<unsigned int>> choices;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(map_cons(
        std::declval<typename List<unsigned int>::Cons &>().d_a0,
        List<std::shared_ptr<List<unsigned int>>>::cons(
            List<unsigned int>::nil(),
            List<std::shared_ptr<List<unsigned int>>>::nil()))) _s0;
  };

  struct _Call2 {
    std::shared_ptr<List<unsigned int>> _s0;
    std::shared_ptr<List<unsigned int>> _s1;
    unsigned int _s2;
    decltype(std::declval<typename List<unsigned int>::Cons &>().d_a0) _s3;
  };

  struct _Call3 {
    std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _s0;
    decltype(std::declval<typename List<unsigned int>::Cons &>().d_a0) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{orig, choices, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> orig = _f.orig;
      const std::shared_ptr<List<unsigned int>> choices = _f.choices;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<std::shared_ptr<List<unsigned int>>>::nil();
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                choices->v())) {
          _result = List<std::shared_ptr<List<unsigned int>>>::nil();
        } else {
          const auto &_m =
              *std::get_if<typename List<unsigned int>::Cons>(&choices->v());
          std::shared_ptr<List<unsigned int>> remaining = remove(_m.d_a0, orig);
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  remaining->v())) {
            _stack.emplace_back(_Call1{map_cons(
                _m.d_a0,
                List<std::shared_ptr<List<unsigned int>>>::cons(
                    List<unsigned int>::nil(),
                    List<std::shared_ptr<List<unsigned int>>>::nil()))});
            _stack.emplace_back(_Enter{orig, _m.d_a1, f});
          } else {
            _stack.emplace_back(_Call2{remaining, remaining, f, _m.d_a0});
            _stack.emplace_back(_Enter{orig, _m.d_a1, f});
          }
        }
      }
    } else if (std::holds_alternative<_Call1>(_frame)) {
      const auto &_f = std::get<_Call1>(_frame);
      _result = _f._s0->app(_result);
    } else if (std::holds_alternative<_Call2>(_frame)) {
      const auto &_f = std::get<_Call2>(_frame);
      _stack.emplace_back(_Call3{_result, _f._s3});
      _stack.emplace_back(_Enter{_f._s0, _f._s1, _f._s2});
    } else {
      const auto &_f = std::get<_Call3>(_frame);
      _result = map_cons(_f._s1, _result)->app(_f._s0);
    }
  }
  return _result;
}

/// permutations_fuel fuel l generates all permutations of a list.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyCombinatorics::permutations_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
    return List<std::shared_ptr<List<unsigned int>>>::cons(
        List<unsigned int>::nil(),
        List<std::shared_ptr<List<unsigned int>>>::nil());
  } else {
    return perms_choices_fuel(fuel, l, l);
  }
}

__attribute__((pure)) unsigned int
LoopifyCombinatorics::len_list(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {};

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
        _stack.emplace_back(_Call1{});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_result + 1);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyCombinatorics::factorial_impl(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 1u;
      } else {
        unsigned int m = n - 1;
        _stack.emplace_back(_Call1{n});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 * _result);
    }
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyCombinatorics::permutations(
    const std::shared_ptr<List<unsigned int>> &l) {
  return permutations_fuel(factorial_impl(len_list(l)), l);
}

/// subsequences l generates all subsequences (subsets preserving order).
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyCombinatorics::subsequences(
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
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
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        _stack.emplace_back(_Call1{_m});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename List<unsigned int>::Cons _m = _f._s0;
      std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> rest = _result;
      std::function<std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>(
          std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>)>
          map_prepend;
      map_prepend =
          [&](std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> lst)
          -> std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> {
        struct _Enter {
          std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> lst;
        };
        struct _Call1 {
          decltype(List<unsigned int>::cons(
              _m.d_a0,
              std::declval<
                  typename List<std::shared_ptr<List<unsigned int>>>::Cons &>()
                  .d_a0)) _s0;
        };
        using _Frame = std::variant<_Enter, _Call1>;
        std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
        std::vector<_Frame> _stack;
        _stack.emplace_back(_Enter{lst});
        while (!_stack.empty()) {
          _Frame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<_Enter>(_frame)) {
            const auto &_f = std::get<_Enter>(_frame);
            std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> lst =
                _f.lst;
            if (std::holds_alternative<
                    typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
                    lst->v())) {
              _result = List<std::shared_ptr<List<unsigned int>>>::nil();
            } else {
              const auto &_m0 = *std::get_if<
                  typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                  &lst->v());
              _stack.emplace_back(
                  _Call1{List<unsigned int>::cons(_m.d_a0, _m0.d_a0)});
              _stack.emplace_back(_Enter{_m0.d_a1});
            }
          } else {
            const auto &_f = std::get<_Call1>(_frame);
            _result = List<std::shared_ptr<List<unsigned int>>>::cons(_f._s0,
                                                                      _result);
          }
        }
        return _result;
      };
      _result = rest->app(map_prepend(rest));
    }
  }
  return _result;
}

/// Helper for cartesian product.
std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyCombinatorics::map_pairs(const unsigned int y,
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
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      auto _cell = List<std::pair<unsigned int, unsigned int>>::cons(
          std::make_pair(_m.d_a0, y), nullptr);
      if (_last) {
        std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
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

/// cartesian l1 l2 Cartesian product of two lists.
std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyCombinatorics::cartesian(const std::shared_ptr<List<unsigned int>> &l1,
                                const std::shared_ptr<List<unsigned int>> &l2) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l2;
  };

  struct _Call1 {
    decltype(map_pairs(
        std::declval<typename List<unsigned int>::Cons &>().d_a0,
        std::declval<const std::shared_ptr<List<unsigned int>> &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l2});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l2 = _f.l2;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l2->v())) {
        _result = List<std::pair<unsigned int, unsigned int>>::nil();
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l2->v());
        _stack.emplace_back(_Call1{map_pairs(_m.d_a0, l1)});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = _f._s0->app(_result);
    }
  }
  return _result;
}

/// power_set l generates the power set (all subsets).
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyCombinatorics::power_set(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
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
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        _stack.emplace_back(_Call1{_m});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename List<unsigned int>::Cons _m = _f._s0;
      std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> rest = _result;
      std::function<std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>(
          std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>)>
          map_add_x;
      map_add_x =
          [&](std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> lst)
          -> std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> {
        struct _Enter {
          std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> lst;
        };
        struct _Call1 {
          decltype(List<unsigned int>::cons(
              _m.d_a0,
              std::declval<
                  typename List<std::shared_ptr<List<unsigned int>>>::Cons &>()
                  .d_a0)) _s0;
        };
        using _Frame = std::variant<_Enter, _Call1>;
        std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
        std::vector<_Frame> _stack;
        _stack.emplace_back(_Enter{lst});
        while (!_stack.empty()) {
          _Frame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<_Enter>(_frame)) {
            const auto &_f = std::get<_Enter>(_frame);
            std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> lst =
                _f.lst;
            if (std::holds_alternative<
                    typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
                    lst->v())) {
              _result = List<std::shared_ptr<List<unsigned int>>>::nil();
            } else {
              const auto &_m0 = *std::get_if<
                  typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                  &lst->v());
              _stack.emplace_back(
                  _Call1{List<unsigned int>::cons(_m.d_a0, _m0.d_a0)});
              _stack.emplace_back(_Enter{_m0.d_a1});
            }
          } else {
            const auto &_f = std::get<_Call1>(_frame);
            _result = List<std::shared_ptr<List<unsigned int>>>::cons(_f._s0,
                                                                      _result);
          }
        }
        return _result;
      };
      _result = rest->app(map_add_x(rest));
    }
  }
  return _result;
}

/// insert_everywhere x l inserts x at every position in l.
std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyCombinatorics::insert_everywhere(const unsigned int x,
                                        std::shared_ptr<List<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
    std::shared_ptr<List<unsigned int>> _s1;
    const unsigned int _s2;
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
      std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = List<std::shared_ptr<List<unsigned int>>>::cons(
            List<unsigned int>::cons(x, List<unsigned int>::nil()),
            List<std::shared_ptr<List<unsigned int>>>::nil());
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        _stack.emplace_back(_Call1{_m, l, x});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename List<unsigned int>::Cons _m = _f._s0;
      std::shared_ptr<List<unsigned int>> l = _f._s1;
      const unsigned int x = _f._s2;
      std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> rest = _result;
      std::function<std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>(
          std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>)>
          prepend_y;
      prepend_y =
          [&](std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> lsts)
          -> std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> {
        struct _Enter {
          std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> lsts;
        };
        struct _Call1 {
          decltype(List<unsigned int>::cons(
              _m.d_a0,
              std::declval<
                  typename List<std::shared_ptr<List<unsigned int>>>::Cons &>()
                  .d_a0)) _s0;
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
              const auto &_m0 = *std::get_if<
                  typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                  &lsts->v());
              _stack.emplace_back(
                  _Call1{List<unsigned int>::cons(_m.d_a0, _m0.d_a0)});
              _stack.emplace_back(_Enter{_m0.d_a1});
            }
          } else {
            const auto &_f = std::get<_Call1>(_frame);
            _result = List<std::shared_ptr<List<unsigned int>>>::cons(_f._s0,
                                                                      _result);
          }
        }
        return _result;
      };
      _result = List<std::shared_ptr<List<unsigned int>>>::cons(
          List<unsigned int>::cons(x, l), prepend_y(rest));
    }
  }
  return _result;
}

/// Helper: check if element is in list.
__attribute__((pure)) bool
LoopifyCombinatorics::elem(const unsigned int x,
                           const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<const unsigned int &>() ==
             std::declval<typename List<unsigned int>::Cons &>().d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = false;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        _stack.emplace_back(_Call1{x == _m.d_a0});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 || _result);
    }
  }
  return _result;
}

/// Helper: list length.
__attribute__((pure)) unsigned int
LoopifyCombinatorics::len_impl(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {};

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
        _stack.emplace_back(_Call1{});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_result + 1);
    }
  }
  return _result;
}

/// dedup l removes all duplicates (keeps first occurrence).
std::shared_ptr<List<unsigned int>>
LoopifyCombinatorics::dedup_fuel(const unsigned int fuel,
                                 const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
          _result = List<unsigned int>::nil();
        } else {
          const auto &_m =
              *std::get_if<typename List<unsigned int>::Cons>(&l->v());
          _stack.emplace_back(_Call1{_m});
          _stack.emplace_back(_Enter{_m.d_a1, f});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename List<unsigned int>::Cons _m = _f._s0;
      std::shared_ptr<List<unsigned int>> rest = _result;
      if (elem(_m.d_a0, rest)) {
        _result = std::move(rest);
      } else {
        _result = List<unsigned int>::cons(_m.d_a0, rest);
      }
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyCombinatorics::dedup(const std::shared_ptr<List<unsigned int>> &l) {
  return dedup_fuel(len_impl(l), l);
}
