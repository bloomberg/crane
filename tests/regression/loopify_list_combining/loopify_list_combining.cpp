#include <loopify_list_combining.h>

__attribute__((pure)) List<unsigned int>
LoopifyListCombining::append(const List<unsigned int> &a,
                             List<unsigned int> b) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_a = a;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_a.v())) {
      *(_write) = std::make_unique<List<unsigned int>>(b);
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_a.v());
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(d_a0, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      _loop_a = *(d_a1);
      continue;
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyListCombining::intersperse(unsigned int sep,
                                  const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<unsigned int>>(
            List<unsigned int>::cons(d_a0, List<unsigned int>::nil()));
        break;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        auto _cell1 = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(sep, nullptr));
        std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1 =
            std::move(_cell1);
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>(
                 std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1->v_mut())
                 .d_a1;
        _loop_l = *(d_a1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyListCombining::intercalate(const List<unsigned int> &sep,
                                  const List<List<unsigned int>> &ll) {
  struct _Enter {
    const List<List<unsigned int>> ll;
  };

  struct _Call1 {
    List<unsigned int> _s0;
    const List<unsigned int> _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<unsigned int>> ll = _f.ll;
      if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
              ll.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<List<unsigned int>>::Cons>(ll.v());
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
                _sv.v())) {
          _result = d_a0;
        } else {
          _stack.emplace_back(_Call1{d_a0, sep});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = append(_f._s0, append(_f._s1, _result));
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifyListCombining::concat(const List<List<unsigned int>> &ll) {
  struct _Enter {
    const List<List<unsigned int>> ll;
  };

  struct _Call1 {
    List<unsigned int> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<unsigned int>> ll = _f.ll;
      if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
              ll.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<List<unsigned int>>::Cons>(ll.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = append(_f._s0, _result);
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifyListCombining::mapcat(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    decltype(List<unsigned int>::cons(
        std::declval<unsigned int &>(),
        List<unsigned int>::cons(std::declval<unsigned int &>(),
                                 List<unsigned int>::nil()))) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{List<unsigned int>::cons(
            d_a0, List<unsigned int>::cons(d_a0, List<unsigned int>::nil()))});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = append(_f._s0, _result);
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifyListCombining::interleave_two(List<unsigned int> l1,
                                     List<unsigned int> l2) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  List<unsigned int> _loop_l2 = std::move(l2);
  List<unsigned int> _loop_l1 = std::move(l1);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1.v())) {
      *(_write) = std::make_unique<List<unsigned int>>(_loop_l2);
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1.v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l2.v())) {
        *(_write) = std::make_unique<List<unsigned int>>(_loop_l1);
        break;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2.v());
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a0, nullptr));
        auto _cell1 = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(d_a00, nullptr));
        std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1 =
            std::move(_cell1);
        *(_write) = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>(
                 std::get<typename List<unsigned int>::Cons>((*_write)->v_mut())
                     .d_a1->v_mut())
                 .d_a1;
        List<unsigned int> _next_l2 = *(d_a10);
        List<unsigned int> _next_l1 = *(d_a1);
        _loop_l2 = std::move(_next_l2);
        _loop_l1 = std::move(_next_l1);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyListCombining::concat_sep(unsigned int sep,
                                 const List<List<unsigned int>> &ll) {
  struct _Enter {
    const List<List<unsigned int>> ll;
  };

  struct _Call1 {
    List<unsigned int> _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<List<unsigned int>> ll = _f.ll;
      if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
              ll.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<List<unsigned int>>::Cons>(ll.v());
        auto &&_sv = *(d_a1);
        if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
                _sv.v())) {
          _result = d_a0;
        } else {
          _stack.emplace_back(_Call1{d_a0, sep});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = append(_f._s0, List<unsigned int>::cons(_f._s1, _result));
    }
  }
  return _result;
}
