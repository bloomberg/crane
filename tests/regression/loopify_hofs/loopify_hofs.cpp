#include "loopify_hofs.h"

/// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
bool LoopifyHofs::is_prefix_of(const List<uint64_t> &l1,
                               const List<uint64_t> &l2) {
  const List<uint64_t> *_loop_l2 = &l2;
  const List<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l1->v())) {
      return true;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l2->v())) {
        return false;
      } else {
        const auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l2->v());
        if (a0 == a00) {
          _loop_l2 = a10.get();
          _loop_l1 = a1.get();
        } else {
          return false;
        }
      }
    }
  }
}

/// lookup_all key l finds all values associated with key in association list.
List<uint64_t> LoopifyHofs::lookup_all(
    uint64_t key,
    const List<std::pair<uint64_t, uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<std::pair<uint64_t, uint64_t>> *l;
  };

  /// _Resume1: saves [v], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t v;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified lookup_all: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<std::pair<uint64_t, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(l.v());
        const uint64_t &k = a0.first;
        const uint64_t &v = a0.second;
        if (k == key) {
          _stack.emplace_back(_Resume1{v});
          _stack.emplace_back(_Enter{a1.get()});
        } else {
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.v, _result);
    }
  }
  return _result;
}

/// Helper: get head of list with default.
uint64_t LoopifyHofs::head_default(uint64_t default0, const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return default0;
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return a0;
  }
}

/// subsequences l generates all subsequences of l: 1,2 -> [],[1],[2],[1,2].
List<List<uint64_t>> LoopifyHofs::subsequences(
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
      auto map_cons_x_impl =
          [&](auto &_self_map_cons_x,
              const List<List<uint64_t>> &lsts) -> List<List<uint64_t>> {
        if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                lsts.v())) {
          return List<List<uint64_t>>::nil();
        } else {
          const auto &[a00, a10] =
              std::get<typename List<List<uint64_t>>::Cons>(lsts.v());
          return List<List<uint64_t>>::cons(
              List<uint64_t>::cons(a0, a00),
              _self_map_cons_x(_self_map_cons_x, *a10));
        }
      };
      auto map_cons_x =
          [&](const List<List<uint64_t>> &lsts) -> List<List<uint64_t>> {
        return map_cons_x_impl(map_cons_x_impl, lsts);
      };
      _result = rest.app(map_cons_x(rest));
    }
  }
  return _result;
}

/// Helper: pair element with all elements in list.
List<std::pair<uint64_t, uint64_t>> LoopifyHofs::pair_with_all(
    uint64_t x,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(std::make_pair(std::declval<uint64_t &>(),
                                         std::declval<uint64_t &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<std::pair<uint64_t, uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified pair_with_all: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<std::pair<uint64_t, uint64_t>>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{std::make_pair(x, a0)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<std::pair<uint64_t, uint64_t>>::cons(_f._s0, _result);
    }
  }
  return _result;
}

/// cartesian l1 l2 computes cartesian product of two lists.
List<std::pair<uint64_t, uint64_t>> LoopifyHofs::cartesian(
    const List<uint64_t> &l1,
    const List<uint64_t>
        &l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l1;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(pair_with_all(
        std::declval<uint64_t &>(), std::declval<const List<uint64_t> &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<std::pair<uint64_t, uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l1});
  /// Loopified cartesian: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l1 = *_f.l1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v())) {
        _result = List<std::pair<uint64_t, uint64_t>>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v());
        _stack.emplace_back(_Resume_Cons{pair_with_all(a0, l2)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = _f._s0.app(_result);
    }
  }
  return _result;
}

/// longest_run l finds the longest consecutive run of equal elements.
/// Matches on recursive result to decide behavior.
List<uint64_t> LoopifyHofs::longest_run_fuel(
    uint64_t fuel,
    List<uint64_t>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
    uint64_t fuel;
  };

  /// _Cont2: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont2 {
    uint64_t a0;
  };

  /// _Resume1: saves [a0], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont2, _Resume1>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l, fuel});
  /// Loopified longest_run_fuel: _Enter -> _Cont2 -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> l = std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        uint64_t f = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
          _result = List<uint64_t>::nil();
        } else {
          auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
            _result =
                List<uint64_t>::cons(std::move(a0), List<uint64_t>::nil());
          } else {
            const auto &[a00, a10] =
                std::get<typename List<uint64_t>::Cons>(_sv0.v());
            if (a0 == a00) {
              _stack.emplace_back(_Resume1{std::move(a0)});
              _stack.emplace_back(_Enter{List<uint64_t>::cons(a00, *a10), f});
            } else {
              _stack.emplace_back(_Cont2{a0});
              _stack.emplace_back(_Enter{List<uint64_t>::cons(a00, *a10), f});
            }
          }
        }
      }
    } else if (std::holds_alternative<_Cont2>(_frame)) {
      auto _f = std::move(std::get<_Cont2>(_frame));
      uint64_t a0 = _f.a0;
      List<uint64_t> rec_result = _result;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              rec_result.v_mut())) {
        _result = List<uint64_t>::cons(std::move(a0), List<uint64_t>::nil());
      } else {
        auto &[a01, a11] =
            std::get<typename List<uint64_t>::Cons>(rec_result.v_mut());
        if (std::move(a0) == std::move(a01)) {
          _result = std::move(rec_result);
        } else {
          _result = std::move(rec_result);
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.a0, _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyHofs::longest_run(const List<uint64_t> &l) {
  return longest_run_fuel(l.length(), l);
}

/// power_set l generates all subsets.
List<List<uint64_t>> LoopifyHofs::power_set(
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
      List<List<uint64_t>> sub = _result;
      auto map_cons_x_impl =
          [&](auto &_self_map_cons_x,
              const List<List<uint64_t>> &lsts) -> List<List<uint64_t>> {
        if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                lsts.v())) {
          return List<List<uint64_t>>::nil();
        } else {
          const auto &[a00, a10] =
              std::get<typename List<List<uint64_t>>::Cons>(lsts.v());
          return List<List<uint64_t>>::cons(
              List<uint64_t>::cons(a0, a00),
              _self_map_cons_x(_self_map_cons_x, *a10));
        }
      };
      auto map_cons_x =
          [&](const List<List<uint64_t>> &lsts) -> List<List<uint64_t>> {
        return map_cons_x_impl(map_cons_x_impl, lsts);
      };
      _result = sub.app(map_cons_x(sub));
    }
  }
  return _result;
}
