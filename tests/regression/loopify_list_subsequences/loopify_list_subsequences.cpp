#include <loopify_list_subsequences.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListSubsequences::map_cons_helper(
    const unsigned int x,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_ll = ll;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<
            typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
            _loop_ll->v())) {
      if (_last) {
        std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
            _last->v_mut())
            .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
      } else {
        _head = List<std::shared_ptr<List<unsigned int>>>::nil();
      }
      _continue = false;
    } else {
      const auto &_m = *std::get_if<
          typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
          &_loop_ll->v());
      auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
          List<unsigned int>::cons(x, _m.d_a0), nullptr);
      if (_last) {
        std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
            _last->v_mut())
            .d_a1 = _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      _loop_ll = _m.d_a1;
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListSubsequences::tails(std::shared_ptr<List<unsigned int>> l) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
            _last->v_mut())
            .d_a1 = List<std::shared_ptr<List<unsigned int>>>::cons(
            List<unsigned int>::nil(),
            List<std::shared_ptr<List<unsigned int>>>::nil());
      } else {
        _head = List<std::shared_ptr<List<unsigned int>>>::cons(
            List<unsigned int>::nil(),
            List<std::shared_ptr<List<unsigned int>>>::nil());
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      auto _cell =
          List<std::shared_ptr<List<unsigned int>>>::cons(_loop_l, nullptr);
      if (_last) {
        std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
            _last->v_mut())
            .d_a1 = _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      _loop_l = _m.d_a1;
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListSubsequences::inits_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
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
        _result = List<std::shared_ptr<List<unsigned int>>>::cons(
            List<unsigned int>::nil(),
            List<std::shared_ptr<List<unsigned int>>>::nil());
      } else {
        unsigned int fuel_ = fuel - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
          _result = List<std::shared_ptr<List<unsigned int>>>::cons(
              List<unsigned int>::nil(),
              List<std::shared_ptr<List<unsigned int>>>::nil());
        } else {
          const auto &_m =
              *std::get_if<typename List<unsigned int>::Cons>(&l->v());
          _stack.emplace_back(_Call1{_m});
          _stack.emplace_back(_Enter{_m.d_a1, fuel_});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename List<unsigned int>::Cons _m = _f._s0;
      std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> rest = _result;
      _result = List<std::shared_ptr<List<unsigned int>>>::cons(
          List<unsigned int>::nil(), map_cons_helper(_m.d_a0, rest));
    }
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListSubsequences::inits(const std::shared_ptr<List<unsigned int>> &l) {
  return inits_fuel(l->length(), l);
}

std::shared_ptr<List<unsigned int>> LoopifyListSubsequences::init_list(
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
      auto &&_sv = _m.d_a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::nil();
        } else {
          _head = List<unsigned int>::nil();
        }
        _continue = false;
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

std::shared_ptr<List<unsigned int>>
LoopifyListSubsequences::snoc(const std::shared_ptr<List<unsigned int>> &l,
                              const unsigned int x) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::cons(x, List<unsigned int>::nil());
      } else {
        _head = List<unsigned int>::cons(x, List<unsigned int>::nil());
      }
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
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
  return _head;
}

__attribute__((pure)) unsigned int LoopifyListSubsequences::last_elem(
    const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = 0u;
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      auto &&_sv = _m.d_a1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
        _result = _m.d_a0;
        _continue = false;
      } else {
        _loop_l = _m.d_a1;
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyListSubsequences::nth_elem(
    const unsigned int n, const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      _result = 0u;
      _continue = false;
    } else {
      const auto &_m =
          *std::get_if<typename List<unsigned int>::Cons>(&_loop_l->v());
      if (_loop_n == 0u) {
        _result = _m.d_a0;
        _continue = false;
      } else {
        std::shared_ptr<List<unsigned int>> _next_l = _m.d_a1;
        unsigned int _next_n =
            (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        _loop_l = std::move(_next_l);
        _loop_n = std::move(_next_n);
      }
    }
  }
  return _result;
}

__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifyListSubsequences::split_at(const unsigned int n,
                                  std::shared_ptr<List<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l;
    const unsigned int n;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<List<unsigned int>>,
            std::shared_ptr<List<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l, n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      std::shared_ptr<List<unsigned int>> l = _f.l;
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = std::make_pair(List<unsigned int>::nil(), std::move(l));
      } else {
        unsigned int n_ = n - 1;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
          _result = std::make_pair(List<unsigned int>::nil(),
                                   List<unsigned int>::nil());
        } else {
          const auto &_m =
              *std::get_if<typename List<unsigned int>::Cons>(&l->v());
          _stack.emplace_back(_Call1{_m});
          _stack.emplace_back(_Enter{_m.d_a1, n_});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      const typename List<unsigned int>::Cons _m = _f._s0;
      const std::shared_ptr<List<unsigned int>> &before = _result.first;
      const std::shared_ptr<List<unsigned int>> &after = _result.second;
      _result =
          std::make_pair(List<unsigned int>::cons(_m.d_a0, before), after);
    }
  }
  return _result;
}
