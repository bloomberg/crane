#include <loopify_list_subsequences.h>

List<List<unsigned int>>
LoopifyListSubsequences::map_cons_helper(unsigned int x,
                                         const List<List<unsigned int>> &ll) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  const List<List<unsigned int>> *_loop_ll = &ll;
  while (true) {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            _loop_ll->v())) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<unsigned int>>::Cons>(_loop_ll->v());
      auto _cell = std::make_unique<List<List<unsigned int>>>(
          typename List<List<unsigned int>>::Cons(
              List<unsigned int>::cons(x, d_a0), nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<List<unsigned int>>::Cons>((*_write)->v_mut())
               .d_a1;
      _loop_ll = d_a1.get();
      continue;
    }
  }
  return std::move(*(_head));
}

List<List<unsigned int>> LoopifyListSubsequences::tails(List<unsigned int> l) {
  std::unique_ptr<List<List<unsigned int>>> _head{};
  std::unique_ptr<List<List<unsigned int>>> *_write = &_head;
  List<unsigned int> _loop_l = std::move(l);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l.v_mut())) {
      *(_write) = std::make_unique<List<List<unsigned int>>>(
          List<List<unsigned int>>::cons(List<unsigned int>::nil(),
                                         List<List<unsigned int>>::nil()));
      break;
    } else {
      auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v_mut());
      auto _cell = std::make_unique<List<List<unsigned int>>>(
          typename List<List<unsigned int>>::Cons(_loop_l, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<List<unsigned int>>::Cons>((*_write)->v_mut())
               .d_a1;
      _loop_l = std::move(*(d_a1));
      continue;
    }
  }
  return std::move(*(_head));
}

List<List<unsigned int>>
LoopifyListSubsequences::inits_fuel(const unsigned int &fuel,
                                    const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
    unsigned int fuel;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<List<unsigned int>>::cons(
            List<unsigned int>::nil(), List<List<unsigned int>>::nil());
      } else {
        unsigned int fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<List<unsigned int>>::cons(
              List<unsigned int>::nil(), List<List<unsigned int>>::nil());
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{d_a1.get(), fuel_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
      List<List<unsigned int>> rest = _result;
      _result = List<List<unsigned int>>::cons(
          List<unsigned int>::nil(), map_cons_helper(d_a0, std::move(rest)));
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
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
        *(_write) =
            std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
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

List<unsigned int> LoopifyListSubsequences::snoc(const List<unsigned int> &l,
                                                 unsigned int x) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *(_write) = std::make_unique<List<unsigned int>>(
          List<unsigned int>::cons(x, List<unsigned int>::nil()));
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(d_a0, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      _loop_l = d_a1.get();
      continue;
    }
  }
  return std::move(*(_head));
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
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
        _result = d_a0;
        break;
      } else {
        _loop_l = d_a1.get();
      }
    }
  }
  return _result;
}

unsigned int LoopifyListSubsequences::nth_elem(const unsigned int &n,
                                               const List<unsigned int> &l) {
  unsigned int _result;
  const List<unsigned int> *_loop_l = &l;
  unsigned int _loop_n = n;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = 0u;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (_loop_n == 0u) {
        _result = d_a0;
        break;
      } else {
        const List<unsigned int> *_next_l = d_a1.get();
        unsigned int _next_n =
            (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        _loop_l = _next_l;
        _loop_n = std::move(_next_n);
      }
    }
  }
  return _result;
}

std::pair<List<unsigned int>, List<unsigned int>>
LoopifyListSubsequences::split_at(const unsigned int &n, List<unsigned int> l) {
  struct _Enter {
    List<unsigned int> l;
    unsigned int n;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<List<unsigned int>, List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l, n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      List<unsigned int> l = std::move(_f.l);
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = std::make_pair(List<unsigned int>::nil(), std::move(l));
      } else {
        unsigned int n_ = n - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                l.v_mut())) {
          _result = std::make_pair(List<unsigned int>::nil(),
                                   List<unsigned int>::nil());
        } else {
          auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v_mut());
          _stack.emplace_back(_Call1{d_a0});
          _stack.emplace_back(_Enter{*(d_a1), n_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
      const List<unsigned int> &before = _result.first;
      const List<unsigned int> &after = _result.second;
      _result = std::make_pair(List<unsigned int>::cons(d_a0, before), after);
    }
  }
  return _result;
}
