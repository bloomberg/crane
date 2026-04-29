#include <loopify_grouping.h>

__attribute__((pure)) List<List<unsigned int>>
LoopifyGrouping::prepend_to_groups(unsigned int x, const bool &same,
                                   List<List<unsigned int>> groups) {
  if (same) {
    if (std::holds_alternative<typename List<List<unsigned int>>::Nil>(
            groups.v_mut())) {
      return List<List<unsigned int>>::cons(
          List<unsigned int>::cons(x, List<unsigned int>::nil()),
          List<List<unsigned int>>::nil());
    } else {
      auto &[d_a0, d_a1] =
          std::get<typename List<List<unsigned int>>::Cons>(groups.v_mut());
      return List<List<unsigned int>>::cons(List<unsigned int>::cons(x, d_a0),
                                            *(d_a1));
    }
  } else {
    return List<List<unsigned int>>::cons(
        List<unsigned int>::cons(x, List<unsigned int>::nil()),
        std::move(groups));
  }
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyGrouping::group_fuel(const unsigned int &fuel,
                            const List<unsigned int> &l) {
  struct _Enter {
    List<unsigned int> l;
    unsigned int fuel;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = _f.l;
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<List<unsigned int>>::nil();
      } else {
        unsigned int fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<List<unsigned int>>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          auto &&_sv0 = *(d_a1);
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv0.v())) {
            _result = List<List<unsigned int>>::cons(
                List<unsigned int>::cons(d_a0, List<unsigned int>::nil()),
                List<List<unsigned int>>::nil());
          } else {
            const auto &[d_a00, d_a10] =
                std::get<typename List<unsigned int>::Cons>(_sv0.v());
            _stack.emplace_back(_Call1{d_a0, d_a00});
            _stack.emplace_back(
                _Enter{List<unsigned int>::cons(d_a00, *(d_a10)), fuel_});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
      unsigned int d_a00 = std::move(_f._s1);
      List<List<unsigned int>> rec_result = _result;
      _result = prepend_to_groups(d_a0, d_a0 == d_a00, std::move(rec_result));
    }
  }
  return _result;
}

__attribute__((pure)) List<List<unsigned int>>
LoopifyGrouping::group(const List<unsigned int> &l) {
  return group_fuel(l.length(), l);
}

__attribute__((pure)) bool LoopifyGrouping::elem(const unsigned int &x,
                                                 const List<unsigned int> &l) {
  bool _result;
  const List<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = false;
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (x == d_a0) {
        _result = true;
        break;
      } else {
        _loop_l = d_a1.get();
      }
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifyGrouping::nub(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
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

__attribute__((pure)) List<unsigned int>
LoopifyGrouping::remove_elem(const unsigned int &x,
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
        _loop_l = d_a1.get();
        continue;
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

__attribute__((pure))
std::pair<std::pair<List<unsigned int>, List<unsigned int>>, List<unsigned int>>
LoopifyGrouping::partition3(const unsigned int &pivot,
                            const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::pair<List<unsigned int>, List<unsigned int>>,
            List<unsigned int>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = std::make_pair(std::make_pair(List<unsigned int>::nil(),
                                                List<unsigned int>::nil()),
                                 List<unsigned int>::nil());
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{d_a0, pivot});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int d_a0 = std::move(_f._s0);
      const unsigned int &pivot = _f._s1;
      const std::pair<List<unsigned int>, List<unsigned int>> &p =
          _result.first;
      const List<unsigned int> &greater = _result.second;
      const List<unsigned int> &less = p.first;
      const List<unsigned int> &equal = p.second;
      if (d_a0 < pivot) {
        _result = std::make_pair(
            std::make_pair(List<unsigned int>::cons(d_a0, less), equal),
            greater);
      } else {
        if (pivot < d_a0) {
          _result = std::make_pair(std::make_pair(less, equal),
                                   List<unsigned int>::cons(d_a0, greater));
        } else {
          _result = std::make_pair(
              std::make_pair(less, List<unsigned int>::cons(d_a0, equal)),
              greater);
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyGrouping::count_elem(const unsigned int &x,
                            const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> *l;
  };

  struct _Call1 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{&l});
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
        if (x == d_a0) {
          _stack.emplace_back(_Call1{1u});
          _stack.emplace_back(_Enter{d_a1.get()});
        } else {
          _stack.emplace_back(_Enter{d_a1.get()});
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

__attribute__((pure)) List<std::pair<unsigned int, unsigned int>>
LoopifyGrouping::group_pairs(const List<unsigned int> &l) {
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
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
        *(_write) =
            std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                List<std::pair<unsigned int, unsigned int>>::nil());
        break;
      } else {
        auto &&_sv1 = *(d_a1);
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv1.v())) {
          *(_write) =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  List<std::pair<unsigned int, unsigned int>>::nil());
          break;
        } else {
          const auto &[d_a01, d_a11] =
              std::get<typename List<unsigned int>::Cons>(_sv1.v());
          auto _cell =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  typename List<std::pair<unsigned int, unsigned int>>::Cons(
                      std::make_pair(d_a0, d_a01), nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<
                   typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                   (*_write)->v_mut())
                   .d_a1;
          _loop_l = d_a11.get();
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}
