#include <loopify_grouping.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyGrouping::prepend_to_groups(
    const unsigned int x, const bool same,
    std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> groups) {
  if (same) {
    if (std::holds_alternative<
            typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
            groups->v()) &&
        groups.use_count() == 1) {
      auto &_rf = std::get<1>(groups->v_mut());
      std::shared_ptr<List<unsigned int>> g = std::move(_rf.d_a0);
      std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> gs =
          std::move(_rf.d_a1);
      _rf.d_a0 = List<unsigned int>::cons(x, g);
      _rf.d_a1 = std::move(gs);
      return groups;
    } else if (std::holds_alternative<
                   typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
                   groups->v())) {
      return List<std::shared_ptr<List<unsigned int>>>::cons(
          List<unsigned int>::cons(x, List<unsigned int>::nil()),
          List<std::shared_ptr<List<unsigned int>>>::nil());
    } else {
      const auto &_m = *std::get_if<
          typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
          &groups->v());
      return List<std::shared_ptr<List<unsigned int>>>::cons(
          List<unsigned int>::cons(x, _m.d_a0), _m.d_a1);
    }
  } else {
    return List<std::shared_ptr<List<unsigned int>>>::cons(
        List<unsigned int>::cons(x, List<unsigned int>::nil()), groups);
  }
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyGrouping::group_fuel(const unsigned int fuel,
                            const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
    const typename List<unsigned int>::Cons _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<std::shared_ptr<List<unsigned int>>>::nil();
      } else {
        unsigned int fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
          _result = List<std::shared_ptr<List<unsigned int>>>::nil();
        } else {
          const auto &_m =
              *std::get_if<typename List<unsigned int>::Cons>(&l->v());
          auto &&_sv0 = _m.d_a1;
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv0->v())) {
            _result = List<std::shared_ptr<List<unsigned int>>>::cons(
                List<unsigned int>::cons(_m.d_a0, List<unsigned int>::nil()),
                List<std::shared_ptr<List<unsigned int>>>::nil());
          } else {
            const auto &_m0 =
                *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
            _stack.emplace_back(_Call1{_m, _m0});
            _stack.emplace_back(
                _Enter{List<unsigned int>::cons(_m0.d_a0, _m0.d_a1), fuel_});
          }
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename List<unsigned int>::Cons _m = _f._s0;
      const typename List<unsigned int>::Cons _m0 = _f._s1;
      std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> rec_result =
          _result;
      _result = prepend_to_groups(_m.d_a0, _m.d_a0 == _m0.d_a0,
                                  std::move(rec_result));
    }
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyGrouping::group(const std::shared_ptr<List<unsigned int>> &l) {
  return group_fuel(l->length(), l);
}

__attribute__((pure)) bool
LoopifyGrouping::elem(const unsigned int x,
                      const std::shared_ptr<List<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = false;
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      if (x == _m.d_a0) {
        _result = true;
        _continue = false;
      } else {
        _loop_l = _m.d_a1;
      }
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyGrouping::nub(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        _stack.emplace_back(_Call1{_m});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename List<unsigned int>::Cons _m = _f._s0;
      std::shared_ptr<List<unsigned int>> rest = _result;
      if (elem(_m.d_a0, rest)) {
        _result = std::move(rest);
      } else {
        _result = List<unsigned int>::cons(_m.d_a0, rest);
      }
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyGrouping::remove_elem(const unsigned int x,
                             const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      if (x == _m.d_a0) {
        _loop_l = _m.d_a1;
        continue;
      } else {
        auto _cell = List<unsigned int>::cons(_m.d_a0, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_l = _m.d_a1;
        continue;
      }
    }
  }
  return _head;
}

__attribute__((pure)) std::pair<std::pair<std::shared_ptr<List<unsigned int>>,
                                          std::shared_ptr<List<unsigned int>>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifyGrouping::partition3(const unsigned int pivot,
                            const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const unsigned int _s0;
    const typename List<unsigned int>::Cons _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::pair<std::shared_ptr<List<unsigned int>>,
                      std::shared_ptr<List<unsigned int>>>,
            std::shared_ptr<List<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = std::make_pair(std::make_pair(List<unsigned int>::nil(),
                                                List<unsigned int>::nil()),
                                 List<unsigned int>::nil());
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        _stack.emplace_back(_Call1{pivot, _m});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const unsigned int pivot = _f._s0;
      const typename List<unsigned int>::Cons _m = _f._s1;
      const std::pair<std::shared_ptr<List<unsigned int>>,
                      std::shared_ptr<List<unsigned int>>> &p = _result.first;
      const std::shared_ptr<List<unsigned int>> &greater = _result.second;
      const std::shared_ptr<List<unsigned int>> &less = p.first;
      const std::shared_ptr<List<unsigned int>> &equal = p.second;
      if (_m.d_a0 < pivot) {
        _result = std::make_pair(
            std::make_pair(List<unsigned int>::cons(_m.d_a0, less), equal),
            greater);
      } else {
        if (pivot < _m.d_a0) {
          _result = std::make_pair(std::make_pair(less, equal),
                                   List<unsigned int>::cons(_m.d_a0, greater));
        } else {
          _result = std::make_pair(
              std::make_pair(less, List<unsigned int>::cons(_m.d_a0, equal)),
              greater);
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyGrouping::count_elem(const unsigned int x,
                            const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(1u) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<unsigned int>> l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
        _result = 0u;
      } else {
        const auto &_m =
            *std::get_if<typename List<unsigned int>::Cons>(&l->v());
        if (x == _m.d_a0) {
          _stack.emplace_back(_Call1{1u});
          _stack.emplace_back(_Enter{_m.d_a1});
        } else {
          _stack.emplace_back(_Enter{_m.d_a1});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyGrouping::group_pairs(const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
            _last->v_mut())
            .d_a1 = List<std::pair<unsigned int, unsigned int>>::nil();
      } else {
        _head = List<std::pair<unsigned int, unsigned int>>::nil();
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      auto &&_sv = _m.d_a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
        if (_last) {
          std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              _last->v_mut())
              .d_a1 = List<std::pair<unsigned int, unsigned int>>::nil();
        } else {
          _head = List<std::pair<unsigned int, unsigned int>>::nil();
        }
        _continue = false;
      } else {
        auto &&_sv1 = _m.d_a1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _sv1->v())) {
          if (_last) {
            std::get<
                typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                _last->v_mut())
                .d_a1 = List<std::pair<unsigned int, unsigned int>>::nil();
          } else {
            _head = List<std::pair<unsigned int, unsigned int>>::nil();
          }
          _continue = false;
        } else {
          const auto &_m1 =
              *std::get_if<typename List<unsigned int>::Cons>(&_sv1->v());
          auto _cell = List<std::pair<unsigned int, unsigned int>>::cons(
              std::make_pair(_m.d_a0, _m1.d_a0), nullptr);
          if (_last) {
            std::get<
                typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                _last->v_mut())
                .d_a1 = _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          _loop_l = _m1.d_a1;
          continue;
        }
      }
    }
  }
  return _head;
}
