#include "loopify_list_combining.h"

List<uint64_t> LoopifyListCombining::append(
    const List<uint64_t> &a,
    List<uint64_t>
        b) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> b;
    const List<uint64_t> *a;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(b), &a});
  /// Loopified append: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> b = std::move(_f.b);
      const List<uint64_t> &a = *_f.a;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(a.v())) {
        _result = std::move(b);
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(a.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{std::move(b), a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f.a0, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListCombining::intersperse(
    uint64_t sep,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0, sep], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
    uint64_t sep;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified intersperse: _Enter -> _Resume_Cons.
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
          _result = List<uint64_t>::cons(a0, List<uint64_t>::nil());
        } else {
          _stack.emplace_back(_Resume_Cons{a0, sep});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(
          _f.a0, List<uint64_t>::cons(_f.sep, std::move(_result)));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListCombining::intercalate(
    const List<uint64_t> &sep,
    const List<List<uint64_t>>
        &ll) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<uint64_t>> *ll;
  };

  /// _Resume_Cons: saves [a0, sep], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> a0;
    List<uint64_t> sep;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&ll});
  /// Loopified intercalate: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                _sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_Resume_Cons{a0, sep});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = append(std::move(_f.a0),
                       append(std::move(_f.sep), std::move(_result)));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListCombining::concat(
    const List<List<uint64_t>>
        &ll) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<uint64_t>> *ll;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&ll});
  /// Loopified concat: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = append(std::move(_f.a0), std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListCombining::mapcat(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(List<uint64_t>::cons(
        std::declval<uint64_t &>(),
        List<uint64_t>::cons(std::declval<uint64_t &>(),
                             List<uint64_t>::nil())))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified mapcat: _Enter -> _Resume_Cons.
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
        _stack.emplace_back(_Resume_Cons{List<uint64_t>::cons(
            a0, List<uint64_t>::cons(a0, List<uint64_t>::nil()))});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = append(_f._s0, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListCombining::interleave_two(
    List<uint64_t> l1,
    List<uint64_t>
        l2) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<uint64_t> l2;
    List<uint64_t> l1;
  };

  /// _Resume_Cons: saves [a0, a00], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
    uint64_t a00;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{std::move(l2), std::move(l1)});
  /// Loopified interleave_two: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<uint64_t> l2 = std::move(_f.l2);
      List<uint64_t> l1 = std::move(_f.l1);
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l1.v_mut())) {
        _result = std::move(l2);
      } else {
        auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l1.v_mut());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l2.v_mut())) {
          _result = std::move(l1);
        } else {
          auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(l2.v_mut());
          _stack.emplace_back(_Resume_Cons{std::move(a0), std::move(a00)});
          _stack.emplace_back(_Enter{*a10, *a1});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(
          _f.a0, List<uint64_t>::cons(_f.a00, std::move(_result)));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListCombining::concat_sep(
    uint64_t sep,
    const List<List<uint64_t>>
        &ll) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<List<uint64_t>> *ll;
  };

  /// _Resume_Cons: saves [a0, sep], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> a0;
    uint64_t sep;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&ll});
  /// Loopified concat_sep: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<uint64_t>> &ll = *_f.ll;
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(ll.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(ll.v());
        auto &&_sv = *a1;
        if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                _sv.v())) {
          _result = std::move(a0);
        } else {
          _stack.emplace_back(_Resume_Cons{a0, sep});
          _stack.emplace_back(_Enter{a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = append(std::move(_f.a0),
                       List<uint64_t>::cons(_f.sep, std::move(_result)));
    }
  }
  return _result;
}
