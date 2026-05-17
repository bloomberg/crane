#include "loopify_list_subsequences.h"

List<List<unsigned int>>
LoopifyListSubsequences::map_cons_helper(unsigned int x,
                                         const List<List<unsigned int>> &ll) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  const List<List<unsigned int>> *_loop_ll = &ll;
  while (true) {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            _loop_ll->v())) {
      *_write = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<List<unsigned int>>::Cons>(_loop_ll->v());
      auto _cell = std::make_unique<List<List<unsigned int>>>(
          typename List<List<unsigned int>>::Cons(
              List<unsigned int>::cons(x, a0), nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<List<unsigned int>>::Cons>((*_write)->v_mut())
               .a1;
      _loop_ll = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

List<List<unsigned int>> LoopifyListSubsequences::tails(List<unsigned int> l) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<unsigned int> _loop_l = std::move(l);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l.v_mut())) {
      *_write = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::cons(List<unsigned int>::nil(),
                                         List<List<unsigned int>>::nil()));
      break;
    } else {
      auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v_mut());
      auto _cell = std::make_unique<List<List<unsigned int>>>(
          typename List<List<unsigned int>>::Cons(_loop_l, nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<List<unsigned int>>::Cons>((*_write)->v_mut())
               .a1;
      _loop_l = std::move(*a1);
      continue;
    }
  }
  return std::move(*_head);
}

List<List<unsigned int>> LoopifyListSubsequences::inits_fuel(
    unsigned int fuel,
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
    unsigned int fuel;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  List<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, fuel});
  /// Loopified inits_fuel: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *_f.l;
      unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<List<unsigned int>>::cons(
            List<unsigned int>::nil(), List<List<unsigned int>>::nil());
      } else {
        unsigned int fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<List<unsigned int>>::cons(
              List<unsigned int>::nil(), List<List<unsigned int>>::nil());
        } else {
          const auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{a1.get(), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      List<List<unsigned int>> rest = _result;
      _result = List<List<unsigned int>>::cons(
          List<unsigned int>::nil(), map_cons_helper(a0, std::move(rest)));
    }
  }
  return _result;
}

List<List<unsigned int>>
LoopifyListSubsequences::inits(const List<unsigned int> &l) {
  return inits_fuel(l.length(), l);
}

List<unsigned int>
LoopifyListSubsequences::init_list(const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
        *_write =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
        break;
      } else {
        auto _cell = std::make_unique<List<unsigned int>>(
            typename List<unsigned int>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write =
            &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
        _loop_l = a1.get();
        continue;
      }
    }
  }
  return std::move(*_head);
}

List<unsigned int> LoopifyListSubsequences::snoc(const List<unsigned int> &l,
                                                 unsigned int x) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<List<unsigned int>>(
          List<unsigned int>::cons(x, List<unsigned int>::nil()));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(a0, nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).a1;
      _loop_l = a1.get();
      continue;
    }
  }
  return std::move(*_head);
}

unsigned int LoopifyListSubsequences::last_elem(const List<unsigned int> &l) {
  unsigned int _result;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = 0u;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
        _result = a0;
        break;
      } else {
        _loop_l = a1.get();
      }
    }
  }
  return _result;
}

unsigned int LoopifyListSubsequences::nth_elem(unsigned int n,
                                               const List<unsigned int> &l) {
  unsigned int _result;
  const List<unsigned int> *_loop_l = &l;
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = 0u;
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (_loop_n == 0u) {
        _result = a0;
        break;
      } else {
        _loop_l = a1.get();
        _loop_n = (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
      }
    }
  }
  return _result;
}

std::pair<List<unsigned int>, List<unsigned int>>
LoopifyListSubsequences::split_at(
    unsigned int n,
    List<unsigned int>
        l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    List<unsigned int> l;
    unsigned int n;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    unsigned int a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<List<unsigned int>, List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{l, n});
  /// Loopified split_at: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<unsigned int> l = std::move(_f.l);
      unsigned int n = _f.n;
      if (n <= 0) {
        _result = std::make_pair(List<unsigned int>::nil(), std::move(l));
      } else {
        unsigned int n_ = n - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                l.v_mut())) {
          _result = std::make_pair(List<unsigned int>::nil(),
                                   List<unsigned int>::nil());
        } else {
          auto &[a0, a1] =
              std::get<typename List<unsigned int>::Cons>(l.v_mut());
          _stack.emplace_back(_Cont_Cons{a0});
          _stack.emplace_back(_Enter{std::move(*a1), n_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      unsigned int a0 = _f.a0;
      const List<unsigned int> &before = _result.first;
      const List<unsigned int> &after = _result.second;
      _result = std::make_pair(List<unsigned int>::cons(std::move(a0), before),
                               after);
    }
  }
  return _result;
}
