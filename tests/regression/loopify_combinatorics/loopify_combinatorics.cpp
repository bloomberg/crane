#include "loopify_combinatorics.h"

/// Consolidated combinatorial algorithms.
/// remove x l removes first occurrence of x from list.
List<uint64_t> LoopifyCombinatorics::remove(uint64_t x,
                                            const List<uint64_t> &l) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (x == a0) {
        *_write = std::make_shared<List<uint64_t>>(*a1);
        break;
      } else {
        auto _cell = std::make_shared<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

/// Helper: prepend x to each list in lsts.
List<List<uint64_t>>
LoopifyCombinatorics::map_cons(uint64_t x, const List<List<uint64_t>> &lsts) {
  std::shared_ptr<List<List<uint64_t>>> _head{};
  std::shared_ptr<List<List<uint64_t>>> *_write = &_head;
  const List<List<uint64_t>> *_loop_lsts = &lsts;
  while (true) {
    if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
            _loop_lsts->v())) {
      *_write =
          std::make_shared<List<List<uint64_t>>>(List<List<uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<uint64_t>>::Cons>(_loop_lsts->v());
      auto _cell = std::make_shared<List<List<uint64_t>>>(
          typename List<List<uint64_t>>::Cons(List<uint64_t>::cons(x, a0),
                                              nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<List<uint64_t>>::Cons>((*_write)->v_mut()).l;
      _loop_lsts = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

/// perms_choices_fuel fuel choices orig generates permutations by iterating
/// over choices.  Single self-recursive function that handles both the choice
/// iteration and the recursive subproblem, enabling full loopification.
/// The match on remaining is hoisted out of the let-binding so that all
/// recursive calls appear at the top level of each branch.
List<List<uint64_t>> LoopifyCombinatorics::perms_choices_fuel(
    uint64_t fuel, const List<uint64_t> &choices,
    const List<uint64_t> &
        orig) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> orig;
    List<uint64_t> choices;
    uint64_t fuel;
  };

  /// _After_Cons: saves [remaining_0, remaining_1, f, a0], dispatches next
  /// recursive call.
  struct _After_Cons {
    List<uint64_t> remaining_0;
    List<uint64_t> remaining_1;
    uint64_t f;
    uint64_t a0;
  };

  /// _Combine_Cons: receives partial results, combines with _result from final
  /// call.
  struct _Combine_Cons {
    List<List<uint64_t>> _result;
    uint64_t a0;
  };

  /// _Resume_Nil: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Nil {
    decltype(map_cons(
        std::declval<uint64_t &>(),
        List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                   List<List<uint64_t>>::nil()))) _s0;
  };

  using _Frame = std::variant<_Enter, _After_Cons, _Combine_Cons, _Resume_Nil>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{orig, choices, fuel});
  /// Loopified perms_choices_fuel: _Enter -> _After_Cons -> _Combine_Cons ->
  /// _Resume_Nil.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &orig = _f.orig;
      const List<uint64_t> &choices = _f.choices;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<List<uint64_t>>::nil();
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(choices.v())) {
          _result = List<List<uint64_t>>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<uint64_t>::Cons>(choices.v());
          List<uint64_t> remaining = remove(a0, orig);
          if (std::holds_alternative<typename List<uint64_t>::Nil>(
                  remaining.v_mut())) {
            _stack.emplace_back(_Resume_Nil{map_cons(
                a0, List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                               List<List<uint64_t>>::nil()))});
            _stack.emplace_back(_Enter{orig, std::move(*a1), f});
          } else {
            _stack.emplace_back(_After_Cons{remaining, remaining, f, a0});
            _stack.emplace_back(_Enter{orig, std::move(*a1), f});
          }
        }
      }
    } else if (std::holds_alternative<_After_Cons>(_frame)) {
      auto _f = std::move(std::get<_After_Cons>(_frame));
      _stack.emplace_back(_Combine_Cons{std::move(_result), _f.a0});
      _stack.emplace_back(
          _Enter{std::move(_f.remaining_0), std::move(_f.remaining_1), _f.f});
    } else if (std::holds_alternative<_Combine_Cons>(_frame)) {
      auto _f = std::move(std::get<_Combine_Cons>(_frame));
      _result = map_cons(_f.a0, std::move(_result)).app(std::move(_f._result));
    } else {
      auto _f = std::move(std::get<_Resume_Nil>(_frame));
      _result = _f._s0.app(_result);
    }
  }
  return _result;
}

/// permutations_fuel fuel l generates all permutations of a list.
List<List<uint64_t>>
LoopifyCombinatorics::permutations_fuel(uint64_t fuel,
                                        const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                      List<List<uint64_t>>::nil());
  } else {
    return perms_choices_fuel(fuel, l, l);
  }
}

uint64_t LoopifyCombinatorics::len_list(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: resumes after recursive call with _result.
  struct _Resume_Cons {};

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified len_list: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}

uint64_t LoopifyCombinatorics::factorial_impl(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [n], resumes after recursive call with _result.
  struct _Resume_m {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified factorial_impl: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Resume_m{n});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = (_f.n * _result);
    }
  }
  return _result;
}

List<List<uint64_t>>
LoopifyCombinatorics::permutations(const List<uint64_t> &l) {
  return permutations_fuel(factorial_impl(len_list(l)), l);
}

/// subsequences l generates all subsequences (subsets preserving order).
List<List<uint64_t>> LoopifyCombinatorics::subsequences(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified subsequences: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                             List<List<uint64_t>>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      List<List<uint64_t>> rest = _result;
      auto map_prepend_impl =
          [&](auto &_self_map_prepend,
              const List<List<uint64_t>> &lst) -> List<List<uint64_t>> {
        if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                lst.v())) {
          return List<List<uint64_t>>::nil();
        } else {
          const auto &[a00, a10] =
              std::get<typename List<List<uint64_t>>::Cons>(lst.v());
          return List<List<uint64_t>>::cons(
              List<uint64_t>::cons(a0, a00),
              _self_map_prepend(_self_map_prepend, *a10));
        }
      };
      auto map_prepend =
          [&](const List<List<uint64_t>> &lst) -> List<List<uint64_t>> {
        return map_prepend_impl(map_prepend_impl, lst);
      };
      _result = rest.app(map_prepend(rest));
    }
  }
  return _result;
}

/// Helper for cartesian product.
List<std::pair<uint64_t, uint64_t>>
LoopifyCombinatorics::map_pairs(uint64_t y, const List<uint64_t> &l) {
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> _head{};
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
          List<std::pair<uint64_t, uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto _cell = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
          typename List<std::pair<uint64_t, uint64_t>>::Cons(
              std::make_pair(a0, y), nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                    (*_write)->v_mut())
                    .l;
      _loop_l = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

/// cartesian l1 l2 Cartesian product of two lists.
List<std::pair<uint64_t, uint64_t>> LoopifyCombinatorics::cartesian(
    const List<uint64_t> &l1,
    const List<uint64_t>
        &l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l2;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(map_pairs(std::declval<uint64_t &>(),
                       std::declval<const List<uint64_t> &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<std::pair<uint64_t, uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l2});
  /// Loopified cartesian: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l2 = *_f.l2;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v())) {
        _result = List<std::pair<uint64_t, uint64_t>>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l2.v());
        _stack.emplace_back(_Resume_Cons{map_pairs(a0, l1)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = _f._s0.app(_result);
    }
  }
  return _result;
}

/// power_set l generates the power set (all subsets).
List<List<uint64_t>> LoopifyCombinatorics::power_set(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified power_set: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                             List<List<uint64_t>>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      List<List<uint64_t>> rest = _result;
      auto map_add_x_impl =
          [&](auto &_self_map_add_x,
              const List<List<uint64_t>> &lst) -> List<List<uint64_t>> {
        if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                lst.v())) {
          return List<List<uint64_t>>::nil();
        } else {
          const auto &[a00, a10] =
              std::get<typename List<List<uint64_t>>::Cons>(lst.v());
          return List<List<uint64_t>>::cons(
              List<uint64_t>::cons(a0, a00),
              _self_map_add_x(_self_map_add_x, *a10));
        }
      };
      auto map_add_x =
          [&](const List<List<uint64_t>> &lst) -> List<List<uint64_t>> {
        return map_add_x_impl(map_add_x_impl, lst);
      };
      _result = rest.app(map_add_x(rest));
    }
  }
  return _result;
}

/// insert_everywhere x l inserts x at every position in l.
List<List<uint64_t>> LoopifyCombinatorics::insert_everywhere(
    uint64_t x,
    List<uint64_t>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
  };

  /// _Cont_Cons: saves [a0, l, x], resumes after recursive call, then processes
  /// rest.
  struct _Cont_Cons {
    uint64_t a0;
    List<uint64_t> l;
    uint64_t x;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l});
  /// Loopified insert_everywhere: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> l = std::move(_f.l);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
        _result = List<List<uint64_t>>::cons(
            List<uint64_t>::cons(x, List<uint64_t>::nil()),
            List<List<uint64_t>>::nil());
      } else {
        auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
        _stack.emplace_back(_Cont_Cons{a0, l, x});
        _stack.emplace_back(_Enter{std::move(*a1)});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      List<uint64_t> l = std::move(_f.l);
      uint64_t x = _f.x;
      List<List<uint64_t>> rest = _result;
      auto prepend_y_impl =
          [&](auto &_self_prepend_y,
              const List<List<uint64_t>> &lsts) -> List<List<uint64_t>> {
        if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                lsts.v())) {
          return List<List<uint64_t>>::nil();
        } else {
          const auto &[a00, a10] =
              std::get<typename List<List<uint64_t>>::Cons>(lsts.v());
          return List<List<uint64_t>>::cons(
              List<uint64_t>::cons(a0, a00),
              _self_prepend_y(_self_prepend_y, *a10));
        }
      };
      auto prepend_y =
          [&](const List<List<uint64_t>> &lsts) -> List<List<uint64_t>> {
        return prepend_y_impl(prepend_y_impl, lsts);
      };
      _result = List<List<uint64_t>>::cons(List<uint64_t>::cons(x, l),
                                           prepend_y(std::move(rest)));
    }
  }
  return _result;
}

/// Helper: check if element is in list.
bool LoopifyCombinatorics::elem(
    uint64_t x,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    decltype(std::declval<uint64_t &>() == std::declval<uint64_t &>()) _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified elem: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = false;
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{x == a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 || _result);
    }
  }
  return _result;
}

/// Helper: list length.
uint64_t LoopifyCombinatorics::len_impl(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: resumes after recursive call with _result.
  struct _Resume_Cons {};

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified len_impl: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}

/// dedup l removes all duplicates (keeps first occurrence).
List<uint64_t> LoopifyCombinatorics::dedup_fuel(
    uint64_t fuel,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t fuel;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, fuel});
  /// Loopified dedup_fuel: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<uint64_t>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get(), f});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      List<uint64_t> rest = _result;
      if (elem(a0, rest)) {
        _result = std::move(rest);
      } else {
        _result = List<uint64_t>::cons(a0, std::move(rest));
      }
    }
  }
  return _result;
}

List<uint64_t> LoopifyCombinatorics::dedup(const List<uint64_t> &l) {
  return dedup_fuel(len_impl(l), l);
}
