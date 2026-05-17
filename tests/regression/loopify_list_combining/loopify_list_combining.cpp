#include "loopify_list_combining.h"

List<uint64_t> LoopifyListCombining::append(const List<uint64_t> &a,
                                            List<uint64_t> b) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_b = std::move(b);
  const List<uint64_t> *_loop_a = &a;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_a->v())) {
      *_write = std::make_unique<List<uint64_t>>(std::move(_loop_b));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_a->v());
      auto _cell = std::make_unique<List<uint64_t>>(
          typename List<uint64_t>::Cons(a0, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).a1;
      _loop_a = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyListCombining::intersperse(uint64_t sep,
                                                 const List<uint64_t> &l) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
        *_write = std::make_unique<List<uint64_t>>(
            List<uint64_t>::cons(a0, List<uint64_t>::nil()));
        break;
      } else {
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(a0, nullptr));
        auto _cell1 = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(sep, nullptr));
        std::get<typename List<uint64_t>::Cons>(_cell->v_mut()).a1 =
            std::move(_cell1);
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>(
                 std::get<typename List<uint64_t>::Cons>((*_write)->v_mut())
                     .a1->v_mut())
                 .a1;
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
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
      _result = append(_f.a0, append(_f.sep, _result));
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
      _result = append(_f.a0, _result);
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
    decltype(List<uint64_t>::cons(
        std::declval<uint64_t &>(),
        List<uint64_t>::cons(std::declval<uint64_t &>(),
                             List<uint64_t>::nil()))) _s0;
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
      _result = append(_f._s0, _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyListCombining::interleave_two(List<uint64_t> l1,
                                                    List<uint64_t> l2) {
  std::unique_ptr<List<uint64_t>> _head{};
  std::unique_ptr<List<uint64_t>> *_write = &_head;
  List<uint64_t> _loop_l2 = std::move(l2);
  List<uint64_t> _loop_l1 = std::move(l1);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(
            _loop_l1.v_mut())) {
      *_write = std::make_unique<List<uint64_t>>(std::move(_loop_l2));
      break;
    } else {
      auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l1.v_mut());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _loop_l2.v_mut())) {
        *_write = std::make_unique<List<uint64_t>>(_loop_l1);
        break;
      } else {
        auto &[a00, a10] =
            std::get<typename List<uint64_t>::Cons>(_loop_l2.v_mut());
        auto _cell = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(std::move(a0), nullptr));
        auto _cell1 = std::make_unique<List<uint64_t>>(
            typename List<uint64_t>::Cons(std::move(a00), nullptr));
        std::get<typename List<uint64_t>::Cons>(_cell->v_mut()).a1 =
            std::move(_cell1);
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<uint64_t>::Cons>(
                 std::get<typename List<uint64_t>::Cons>((*_write)->v_mut())
                     .a1->v_mut())
                 .a1;
        _loop_l2 = std::move(*a10);
        _loop_l1 = std::move(*a1);
        continue;
      }
    }
  }
  return std::move(*_head);
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
      _result = append(_f.a0, List<uint64_t>::cons(_f.sep, _result));
    }
  }
  return _result;
}
