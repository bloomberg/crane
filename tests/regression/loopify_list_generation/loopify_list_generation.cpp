#include <loopify_list_generation.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

std::shared_ptr<List<unsigned int>>
LoopifyListGeneration::replicate(const unsigned int n, const unsigned int x) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell = List<unsigned int>::cons(x, nullptr);
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      _loop_n = n_;
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyListGeneration::stutter(const std::shared_ptr<List<unsigned int>> &l) {
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
      auto _cell = List<unsigned int>::cons(_m.d_a0, nullptr);
      auto _cell1 = List<unsigned int>::cons(_m.d_a0, nullptr);
      std::get<typename List<unsigned int>::Cons>(_cell->v_mut()).d_a1 = _cell1;
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell1;
      _loop_l = _m.d_a1;
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyListGeneration::cycle(const unsigned int n,
                             const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      const auto &_f = std::get<_Enter>(_frame);
      const unsigned int n = _f.n;
      if (n <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int n_ = n - 1;
        _stack.emplace_back(_Call1{l});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = _f._s0->app(_result);
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListGeneration::iterate(const unsigned int n, const unsigned int x) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  unsigned int _loop_x = x;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell = List<unsigned int>::cons(_loop_x, nullptr);
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      unsigned int _next_x = (_loop_x + 1u);
      unsigned int _next_n = n_;
      _loop_x = std::move(_next_x);
      _loop_n = std::move(_next_n);
      continue;
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyListGeneration::replicate_list(
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l) {
  struct _Enter {
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> l;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
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
      const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> l =
          _f.l;
      if (std::holds_alternative<
              typename List<std::pair<unsigned int, unsigned int>>::Nil>(
              l->v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &_m = *std::get_if<
            typename List<std::pair<unsigned int, unsigned int>>::Cons>(
            &l->v());
        const unsigned int &n = _m.d_a0.first;
        const unsigned int &x = _m.d_a0.second;
        std::shared_ptr<List<unsigned int>> rep = replicate(n, x);
        _stack.emplace_back(_Call1{std::move(rep)});
        _stack.emplace_back(_Enter{_m.d_a1});
      }
    } else {
      const auto &_f = std::get<_Call1>(_frame);
      _result = _f._s0->app(_result);
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListGeneration::repeat_with_sep(
    const unsigned int sep, const unsigned int n, const unsigned int x) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      unsigned int n_ = _loop_n - 1;
      if (n_ <= 0) {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::cons(x, List<unsigned int>::nil());
        } else {
          _head = List<unsigned int>::cons(x, List<unsigned int>::nil());
        }
        _continue = false;
      } else {
        unsigned int _x = n_ - 1;
        auto _cell = List<unsigned int>::cons(x, nullptr);
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
        _loop_n = n_;
        continue;
      }
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyListGeneration::range(const unsigned int start, const unsigned int len) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  unsigned int _loop_len = len;
  unsigned int _loop_start = start;
  bool _continue = true;
  while (_continue) {
    if (_loop_len <= 0) {
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            List<unsigned int>::nil();
      } else {
        _head = List<unsigned int>::nil();
      }
      _continue = false;
    } else {
      unsigned int len_ = _loop_len - 1;
      auto _cell = List<unsigned int>::cons(_loop_start, nullptr);
      if (_last) {
        std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
            _cell;
      } else {
        _head = _cell;
      }
      _last = _cell;
      unsigned int _next_len = len_;
      unsigned int _next_start = (_loop_start + 1u);
      _loop_len = std::move(_next_len);
      _loop_start = std::move(_next_start);
      continue;
    }
  }
  return _head;
}
