#include <loopify_combinatorics.h>

/// Consolidated combinatorial algorithms.
/// remove x l removes first occurrence of x from list.
List<unsigned int> LoopifyCombinatorics::remove(const unsigned int x,
                                                const List<unsigned int> &l) {
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
      if (x == d_a0) {
        *(_write) = std::make_unique<List<unsigned int>>(*(d_a1));
        break;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                 .d_a1;
        _loop_l = d_a1.get();
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// Helper: prepend x to each list in lsts.
List<List<unsigned int>>
LoopifyCombinatorics::map_cons(const unsigned int x,
                               const List<List<unsigned int>> &lsts) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  const List<List<unsigned int>> *_loop_lsts = &lsts;
  while (true) {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            _loop_lsts->v())) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<unsigned int>>::Cons>(_loop_lsts->v());
      auto _cell = std::make_unique<List<List<unsigned int>>>(
          typename List<List<unsigned int>>::Cons(
              List<unsigned int>::cons(x, d_a0), nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<List<unsigned int>>::Cons>((*_write)->v_mut())
               .d_a1;
      _loop_lsts = d_a1.get();
      continue;
    }
  }
  return std::move(*(_head));
}

/// perms_choices_fuel fuel choices orig generates permutations by iterating
/// over choices.  Single self-recursive function that handles both the choice
/// iteration and the recursive subproblem, enabling full loopification.
/// The match on remaining is hoisted out of the let-binding so that all
/// recursive calls appear at the top level of each branch.
List<List<unsigned int>>
LoopifyCombinatorics::perms_choices_fuel(const unsigned int fuel,
                                         const List<unsigned int> &choices,
                                         const List<unsigned int> &orig) {
  struct _Enter {
    List<unsigned int> orig;
    List<unsigned int> choices;
    unsigned int fuel;
  };

  /// Intermediate: saves [remaining_0, remaining_1, f, d_a0], dispatches next
  /// recursive call.
  struct _After3 {
    List<unsigned int> remaining_0;
    List<unsigned int> remaining_1;
    unsigned int f;
    unsigned int d_a0;
  };

  /// Combiner: receives first result, combines with second recursive call.
  struct _Combine2 {
    List<List<unsigned int>> _result;
    unsigned int d_a0;
  };

  /// Continuation: saves [_s0] across recursive call.
  struct _Resume1 {
    decltype(map_cons(
        std::declval<unsigned int &>(),
        List<List<unsigned int>>::cons(List<unsigned int>::nil(),
                                       List<List<unsigned int>>::nil()))) _s0;
  };

  using _Frame = std::variant<_Enter, _After3, _Combine2, _Resume1>;
  List<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{orig, choices, fuel});
  /// Frame dispatch: _Enter, _After3, _Combine2, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &orig = _f.orig;
      const List<unsigned int> &choices = _f.choices;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<List<unsigned int>>::nil();
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                choices.v())) {
          _result = List<List<unsigned int>>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(choices.v());
          List<unsigned int> remaining = remove(d_a0, orig);
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  remaining.v_mut())) {
            _stack.emplace_back(
                _Resume1{map_cons(d_a0, List<List<unsigned int>>::cons(
                                            List<unsigned int>::nil(),
                                            List<List<unsigned int>>::nil()))});
            _stack.emplace_back(_Enter{orig, *(d_a1), f});
          } else {
            _stack.emplace_back(_After3{remaining, remaining, f, d_a0});
            _stack.emplace_back(_Enter{orig, *(d_a1), f});
          }
        }
      }
    } else if (std::holds_alternative<_After3>(_frame)) {
      auto _f = std::move(std::get<_After3>(_frame));
      _stack.emplace_back(_Combine2{std::move(_result), _f.d_a0});
      _stack.emplace_back(
          _Enter{std::move(_f.remaining_0), std::move(_f.remaining_1), _f.f});
    } else if (std::holds_alternative<_Combine2>(_frame)) {
      auto _f = std::move(std::get<_Combine2>(_frame));
      _result = map_cons(_f.d_a0, _result).app(_f._result);
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = _f._s0.app(_result);
    }
  }
  return _result;
}

/// permutations_fuel fuel l generates all permutations of a list.
List<List<unsigned int>>
LoopifyCombinatorics::permutations_fuel(const unsigned int fuel,
                                        const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return List<List<unsigned int>>::cons(List<unsigned int>::nil(),
                                          List<List<unsigned int>>::nil());
  } else {
    return perms_choices_fuel(fuel, l, l);
  }
}

unsigned int LoopifyCombinatorics::len_list(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  /// Continuation: saves across recursive call.
  struct _Resume1 {};

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Frame dispatch: _Enter, _Resume1.
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
        _stack.emplace_back(_Resume1{});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}

unsigned int LoopifyCombinatorics::factorial_impl(const unsigned int n) {
  struct _Enter {
    unsigned int n;
  };

  /// Continuation: saves [n] across recursive call.
  struct _Resume1 {
    unsigned int n;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = 1u;
      } else {
        unsigned int m = n - 1;
        _stack.emplace_back(_Resume1{n});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f.n * _result);
    }
  }
  return _result;
}

List<List<unsigned int>>
LoopifyCombinatorics::permutations(const List<unsigned int> &l) {
  return permutations_fuel(factorial_impl(len_list(l)), l);
}

/// subsequences l generates all subsequences (subsets preserving order).
List<List<unsigned int>>
LoopifyCombinatorics::subsequences(const List<unsigned int> &l) {
  struct _Enter {
    List<unsigned int> l;
  };

  /// Continuation: saves [d_a0] across recursive call, then processes rest.
  struct _Cont1 {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  List<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  /// Frame dispatch: _Enter, _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = List<List<unsigned int>>::cons(
            List<unsigned int>::nil(), List<List<unsigned int>>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        List<unsigned int> d_a1_value = List<unsigned int>(*(d_a1));
        _stack.emplace_back(_Cont1{d_a0});
        _stack.emplace_back(_Enter{d_a1_value});
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      unsigned int d_a0 = _f.d_a0;
      List<List<unsigned int>> rest = _result;
      std::function<List<List<unsigned int>>(List<List<unsigned int>>)>
          map_prepend;
      map_prepend =
          [&](List<List<unsigned int>> lst) -> List<List<unsigned int>> {
        struct _Enter {
          List<List<unsigned int>> lst;
        };
        /// Continuation: saves [_s0] across recursive call.
        struct _Resume1 {
          decltype(List<unsigned int>::cons(
              d_a0, std::declval<List<unsigned int> &>())) _s0;
        };
        using _Frame = std::variant<_Enter, _Resume1>;
        List<List<unsigned int>> _result{};
        std::vector<_Frame> _stack;
        _stack.reserve(16);
        _stack.emplace_back(_Enter{lst});
        /// Frame dispatch: _Enter, _Resume1.
        while (!_stack.empty()) {
          _Frame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<_Enter>(_frame)) {
            auto _f = std::move(std::get<_Enter>(_frame));
            List<List<unsigned int>> lst = std::move(_f.lst);
            if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
                    lst.v())) {
              _result = List<List<unsigned int>>::nil();
            } else {
              const auto &[d_a00, d_a10] =
                  std::get<typename List<List<unsigned int>>::Cons>(lst.v());
              _stack.emplace_back(
                  _Resume1{List<unsigned int>::cons(d_a0, d_a00)});
              _stack.emplace_back(_Enter{*(d_a10)});
            }
          } else {
            auto _f = std::move(std::get<_Resume1>(_frame));
            _result = List<List<unsigned int>>::cons(_f._s0, _result);
          }
        }
        return _result;
      };
      _result = rest.app(map_prepend(rest));
    }
  }
  return _result;
}

/// Helper for cartesian product.
List<std::pair<unsigned int, unsigned int>>
LoopifyCombinatorics::map_pairs(const unsigned int y,
                                const List<unsigned int> &l) {
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *(_write) = std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
          List<std::pair<unsigned int, unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto _cell =
          std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
              typename List<std::pair<unsigned int, unsigned int>>::Cons(
                  std::make_pair(d_a0, y), nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
               (*_write)->v_mut())
               .d_a1;
      _loop_l = d_a1.get();
      continue;
    }
  }
  return std::move(*(_head));
}

/// cartesian l1 l2 Cartesian product of two lists.
List<std::pair<unsigned int, unsigned int>>
LoopifyCombinatorics::cartesian(const List<unsigned int> &l1,
                                const List<unsigned int> &l2) {
  struct _Enter {
    const List<unsigned int> *l2;
  };

  /// Continuation: saves [_s0] across recursive call.
  struct _Resume1 {
    decltype(map_pairs(std::declval<unsigned int &>(),
                       std::declval<const List<unsigned int> &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<std::pair<unsigned int, unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l2});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l2 = *(_f.l2);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l2.v())) {
        _result = List<std::pair<unsigned int, unsigned int>>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l2.v());
        _stack.emplace_back(_Resume1{map_pairs(d_a0, l1)});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = _f._s0.app(_result);
    }
  }
  return _result;
}

/// power_set l generates the power set (all subsets).
List<List<unsigned int>>
LoopifyCombinatorics::power_set(const List<unsigned int> &l) {
  struct _Enter {
    List<unsigned int> l;
  };

  /// Continuation: saves [d_a0] across recursive call, then processes rest.
  struct _Cont1 {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  List<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  /// Frame dispatch: _Enter, _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = List<List<unsigned int>>::cons(
            List<unsigned int>::nil(), List<List<unsigned int>>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        List<unsigned int> d_a1_value = List<unsigned int>(*(d_a1));
        _stack.emplace_back(_Cont1{d_a0});
        _stack.emplace_back(_Enter{d_a1_value});
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      unsigned int d_a0 = _f.d_a0;
      List<List<unsigned int>> rest = _result;
      std::function<List<List<unsigned int>>(List<List<unsigned int>>)>
          map_add_x;
      map_add_x =
          [&](List<List<unsigned int>> lst) -> List<List<unsigned int>> {
        struct _Enter {
          List<List<unsigned int>> lst;
        };
        /// Continuation: saves [_s0] across recursive call.
        struct _Resume1 {
          decltype(List<unsigned int>::cons(
              d_a0, std::declval<List<unsigned int> &>())) _s0;
        };
        using _Frame = std::variant<_Enter, _Resume1>;
        List<List<unsigned int>> _result{};
        std::vector<_Frame> _stack;
        _stack.reserve(16);
        _stack.emplace_back(_Enter{lst});
        /// Frame dispatch: _Enter, _Resume1.
        while (!_stack.empty()) {
          _Frame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<_Enter>(_frame)) {
            auto _f = std::move(std::get<_Enter>(_frame));
            List<List<unsigned int>> lst = std::move(_f.lst);
            if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
                    lst.v())) {
              _result = List<List<unsigned int>>::nil();
            } else {
              const auto &[d_a00, d_a10] =
                  std::get<typename List<List<unsigned int>>::Cons>(lst.v());
              _stack.emplace_back(
                  _Resume1{List<unsigned int>::cons(d_a0, d_a00)});
              _stack.emplace_back(_Enter{*(d_a10)});
            }
          } else {
            auto _f = std::move(std::get<_Resume1>(_frame));
            _result = List<List<unsigned int>>::cons(_f._s0, _result);
          }
        }
        return _result;
      };
      _result = rest.app(map_add_x(rest));
    }
  }
  return _result;
}

/// insert_everywhere x l inserts x at every position in l.
List<List<unsigned int>>
LoopifyCombinatorics::insert_everywhere(const unsigned int x,
                                        List<unsigned int> l) {
  struct _Enter {
    List<unsigned int> l;
  };

  /// Continuation: saves [d_a0, l, x] across recursive call, then processes
  /// rest.
  struct _Cont1 {
    unsigned int d_a0;
    List<unsigned int> l;
    unsigned int x;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  List<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  /// Frame dispatch: _Enter, _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<unsigned int> l = std::move(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v_mut())) {
        _result = List<List<unsigned int>>::cons(
            List<unsigned int>::cons(x, List<unsigned int>::nil()),
            List<List<unsigned int>>::nil());
      } else {
        auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v_mut());
        List<unsigned int> d_a1_value = List<unsigned int>(*(d_a1));
        _stack.emplace_back(_Cont1{d_a0, l, x});
        _stack.emplace_back(_Enter{d_a1_value});
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      unsigned int d_a0 = _f.d_a0;
      List<unsigned int> l = std::move(_f.l);
      const unsigned int x = _f.x;
      List<List<unsigned int>> rest = _result;
      std::function<List<List<unsigned int>>(List<List<unsigned int>>)>
          prepend_y;
      prepend_y =
          [&](List<List<unsigned int>> lsts) -> List<List<unsigned int>> {
        struct _Enter {
          List<List<unsigned int>> lsts;
        };
        /// Continuation: saves [_s0] across recursive call.
        struct _Resume1 {
          decltype(List<unsigned int>::cons(
              d_a0, std::declval<List<unsigned int> &>())) _s0;
        };
        using _Frame = std::variant<_Enter, _Resume1>;
        List<List<unsigned int>> _result{};
        std::vector<_Frame> _stack;
        _stack.reserve(16);
        _stack.emplace_back(_Enter{lsts});
        /// Frame dispatch: _Enter, _Resume1.
        while (!_stack.empty()) {
          _Frame _frame = std::move(_stack.back());
          _stack.pop_back();
          if (std::holds_alternative<_Enter>(_frame)) {
            auto _f = std::move(std::get<_Enter>(_frame));
            List<List<unsigned int>> lsts = std::move(_f.lsts);
            if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
                    lsts.v())) {
              _result = List<List<unsigned int>>::nil();
            } else {
              const auto &[d_a00, d_a10] =
                  std::get<typename List<List<unsigned int>>::Cons>(lsts.v());
              _stack.emplace_back(
                  _Resume1{List<unsigned int>::cons(d_a0, d_a00)});
              _stack.emplace_back(_Enter{*(d_a10)});
            }
          } else {
            auto _f = std::move(std::get<_Resume1>(_frame));
            _result = List<List<unsigned int>>::cons(_f._s0, _result);
          }
        }
        return _result;
      };
      _result = List<List<unsigned int>>::cons(List<unsigned int>::cons(x, l),
                                               prepend_y(std::move(rest)));
    }
  }
  return _result;
}

/// Helper: check if element is in list.
bool LoopifyCombinatorics::elem(const unsigned int x,
                                const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  /// Continuation: saves [_s0] across recursive call.
  struct _Resume1 {
    decltype(std::declval<const unsigned int &>() ==
             std::declval<unsigned int &>()) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Frame dispatch: _Enter, _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = false;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Resume1{x == d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_f._s0 || _result);
    }
  }
  return _result;
}

/// Helper: list length.
unsigned int LoopifyCombinatorics::len_impl(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  /// Continuation: saves across recursive call.
  struct _Resume1 {};

  using _Frame = std::variant<_Enter, _Resume1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  /// Frame dispatch: _Enter, _Resume1.
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
        _stack.emplace_back(_Resume1{});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}

/// dedup l removes all duplicates (keeps first occurrence).
List<unsigned int>
LoopifyCombinatorics::dedup_fuel(const unsigned int fuel,
                                 const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
    unsigned int fuel;
  };

  /// Continuation: saves [d_a0] across recursive call, then processes rest.
  struct _Cont1 {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l, fuel});
  /// Frame dispatch: _Enter, _Cont1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int f = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<unsigned int>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Cont1{d_a0});
          _stack.emplace_back(_Enter{d_a1.get(), f});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      unsigned int d_a0 = _f.d_a0;
      List<unsigned int> rest = _result;
      if (elem(d_a0, rest)) {
        _result = std::move(rest);
      } else {
        _result = List<unsigned int>::cons(d_a0, std::move(rest));
      }
    }
  }
  return _result;
}

List<unsigned int> LoopifyCombinatorics::dedup(const List<unsigned int> &l) {
  return dedup_fuel(len_impl(l), l);
}
