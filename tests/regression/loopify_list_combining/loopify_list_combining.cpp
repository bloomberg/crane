#include <loopify_list_combining.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

std::shared_ptr<List<unsigned int>>
LoopifyListCombining::append(const std::shared_ptr<List<unsigned int>> &a,
                             std::shared_ptr<List<unsigned int>> b) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_a = a;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_a->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            std::move(b);
      } else {
        _head = std::move(b);
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_a->v());
      auto _cell = List<unsigned int>::cons(d_a0, nullptr);
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      _loop_a = d_a1;
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyListCombining::intersperse(
    const unsigned int sep, const std::shared_ptr<List<unsigned int>> &l) {
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
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (std::holds_alternative<typename List<unsigned int>::Nil>(d_a1->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
        } else {
          _head = List<unsigned int>::cons(d_a0, List<unsigned int>::nil());
        }
        _continue = false;
      } else {
        auto _cell = List<unsigned int>::cons(d_a0, nullptr);
        auto _cell1 = List<unsigned int>::cons(sep, nullptr);
        std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1 =
            _cell1;
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell1;
        _loop_l = d_a1;
        continue;
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyListCombining::intercalate(
    const std::shared_ptr<List<unsigned int>> &sep,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
    const std::shared_ptr<List<unsigned int>> _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll =
          _f.ll;
      if (std::holds_alternative<
              typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
              ll->v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                ll->v());
        if (std::holds_alternative<
                typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
                d_a1->v())) {
          _result = d_a0;
        } else {
          _stack.emplace_back(_Call1{d_a0, sep});
          _stack.emplace_back(_Enter{d_a1});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = append(_f._s0, append(_f._s1, _result));
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListCombining::concat(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll =
          _f.ll;
      if (std::holds_alternative<
              typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
              ll->v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                ll->v());
        _stack.emplace_back(_Call1{d_a0});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = append(_f._s0, _result);
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListCombining::mapcat(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(List<unsigned int>::cons(
        std::declval<unsigned int &>(),
        List<unsigned int>::cons(std::declval<unsigned int &>(),
                                 List<unsigned int>::nil()))) _s0;
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
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l->v());
        _stack.emplace_back(_Call1{List<unsigned int>::cons(
            d_a0, List<unsigned int>::cons(d_a0, List<unsigned int>::nil()))});
        _stack.emplace_back(_Enter{d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = append(_f._s0, _result);
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListCombining::interleave_two(std::shared_ptr<List<unsigned int>> l1,
                                     std::shared_ptr<List<unsigned int>> l2) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l1->v())) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            std::move(_loop_l2);
      } else {
        _head = std::move(_loop_l2);
      }
      _continue = false;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l1->v());
      if (std::holds_alternative<typename List<unsigned int>::Cons>(
              _loop_l2->v()) &&
          _loop_l2.use_count() == 1) {
        auto &_rf = std::get<1>(_loop_l2->v_mut());
        unsigned int y = std::move(_rf.d_a0);
        std::shared_ptr<List<unsigned int>> ys = std::move(_rf.d_a1);
        _rf.d_a0 = std::move(d_a0);
        _rf.d_a1 = List<unsigned int>::cons(y, interleave_two(d_a1, ys));
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _loop_l2;
        } else {
          _head = _loop_l2;
        }
        _continue = false;
      } else if (std::holds_alternative<typename List<unsigned int>::Nil>(
                     _loop_l2->v())) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              std::move(_loop_l1);
        } else {
          _head = std::move(_loop_l1);
        }
        _continue = false;
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename List<unsigned int>::Cons>(_loop_l2->v());
        auto _cell = List<unsigned int>::cons(d_a0, nullptr);
        auto _cell1 = List<unsigned int>::cons(d_a00, nullptr);
        std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1 =
            _cell1;
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell1;
        std::shared_ptr<List<unsigned int>> _next_l2 = d_a10;
        std::shared_ptr<List<unsigned int>> _next_l1 = d_a1;
        _loop_l2 = std::move(_next_l2);
        _loop_l1 = std::move(_next_l1);
        continue;
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyListCombining::concat_sep(
    const unsigned int sep,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
    const unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll =
          _f.ll;
      if (std::holds_alternative<
              typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
              ll->v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                ll->v());
        if (std::holds_alternative<
                typename List<std::shared_ptr<List<unsigned int>>>::Nil>(
                d_a1->v())) {
          _result = d_a0;
        } else {
          _stack.emplace_back(_Call1{d_a0, sep});
          _stack.emplace_back(_Enter{d_a1});
        }
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = append(_f._s0, List<unsigned int>::cons(_f._s1, _result));
    }
  }
  return _result;
}
