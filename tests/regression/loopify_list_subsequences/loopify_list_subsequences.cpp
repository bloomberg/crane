#include "loopify_list_subsequences.h"

List<List<uint64_t>> LoopifyListSubsequences::map_cons_helper(
    uint64_t x,
    const List<List<uint64_t>>
        &ll) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<uint64_t>> *ll;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(List<uint64_t>::cons(
        std::declval<uint64_t &>(), std::declval<List<uint64_t> &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&ll});
  /// Loopified map_cons_helper: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<List<uint64_t>>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(_Resume_Cons{List<uint64_t>::cons(x, a0)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<List<uint64_t>>::cons(_f._s0, _result);
    }
  }
  return _result;
}

List<List<uint64_t>> LoopifyListSubsequences::tails(
    List<uint64_t>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
  };

  /// _Resume_Cons: saves [l], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> l;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(l)});
  /// Loopified tails: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> l = std::move(_f.l);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
        _result = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                             List<List<uint64_t>>::nil());
      } else {
        auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
        _stack.emplace_back(_Resume_Cons{l});
        _stack.emplace_back(_Enter{*a1});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<List<uint64_t>>::cons(_f.l, _result);
    }
  }
  return _result;
}

List<List<uint64_t>> LoopifyListSubsequences::inits_fuel(
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
  List<List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, fuel});
  /// Loopified inits_fuel: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                             List<List<uint64_t>>::nil());
      } else {
        uint64_t fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                               List<List<uint64_t>>::nil());
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get(), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      List<List<uint64_t>> rest = std::move(_result);
      _result = List<List<uint64_t>>::cons(
          List<uint64_t>::nil(), map_cons_helper(a0, std::move(rest)));
    }
  }
  return _result;
}

List<List<uint64_t>> LoopifyListSubsequences::inits(const List<uint64_t> &l) {
  return inits_fuel(l.length(), l);
}

List<uint64_t> LoopifyListSubsequences::init_list(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified init_list: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
          _result = List<uint64_t>::nil();
        } else {
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f.a0, _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyListSubsequences::snoc(
    const List<uint64_t> &l,
    uint64_t
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified snoc: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::cons(x, List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f.a0, _result);
    }
  }
  return _result;
}

uint64_t LoopifyListSubsequences::last_elem(const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
        return a0;
      } else {
        _loop_l = a1.get();
      }
    }
  }
}

uint64_t LoopifyListSubsequences::nth_elem(uint64_t n,
                                           const List<uint64_t> &l) {
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      if (_loop_n == UINT64_C(0)) {
        return a0;
      } else {
        _loop_l = a1.get();
        _loop_n =
            (((_loop_n - UINT64_C(1)) > _loop_n ? 0 : (_loop_n - UINT64_C(1))));
      }
    }
  }
}

std::pair<List<uint64_t>, List<uint64_t>> LoopifyListSubsequences::split_at(
    uint64_t n,
    List<uint64_t>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l;
    uint64_t n;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<List<uint64_t>, List<uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(l), n});
  /// Loopified split_at: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> l = std::move(_f.l);
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = std::make_pair(List<uint64_t>::nil(), std::move(l));
      } else {
        uint64_t n_ = n - 1;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
          _result =
              std::make_pair(List<uint64_t>::nil(), List<uint64_t>::nil());
        } else {
          auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{*a1, n_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      uint64_t a0 = _f.a0;
      auto _cs = std::move(_result);
      List<uint64_t> before = std::move(_cs.first);
      List<uint64_t> after = std::move(_cs.second);
      _result =
          std::make_pair(List<uint64_t>::cons(std::move(a0), std::move(before)),
                         std::move(after));
    }
  }
  return _result;
}
