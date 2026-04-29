#include <loopify_generators.h>

/// Consolidated list generator functions.
/// cycle n l repeats the list n times: cycle 2 1,2 -> 1,2,1,2.
__attribute__((pure)) List<unsigned int>
LoopifyGenerators::cycle(const unsigned int &n, const List<unsigned int> &l) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const List<unsigned int> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      if (n <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int m = n - 1;
        _stack.emplace_back(_Call1{l});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = _f._s0.app(_result);
    }
  }
  return _result;
}

/// zip_longest l1 l2 default zips, using default for missing elements.
__attribute__((pure)) List<std::pair<unsigned int, unsigned int>>
LoopifyGenerators::zip_longest_aux(const List<unsigned int> &l1,
                                   const List<unsigned int> &l2,
                                   unsigned int default0,
                                   const unsigned int &fuel) {
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> *_write = &_head;
  unsigned int _loop_fuel = fuel;
  List<unsigned int> _loop_l2 = l2;
  List<unsigned int> _loop_l1 = l1;
  while (true) {
    if (_loop_fuel <= 0) {
      *(_write) = std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
          List<std::pair<unsigned int, unsigned int>>::nil());
      break;
    } else {
      unsigned int f = _loop_fuel - 1;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(
              _loop_l1.v())) {
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2.v())) {
          *(_write) =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  List<std::pair<unsigned int, unsigned int>>::nil());
          break;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2.v());
          auto _cell =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  typename List<std::pair<unsigned int, unsigned int>>::Cons(
                      std::make_pair(default0, d_a00), nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<
                   typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                   (*_write)->v_mut())
                   .d_a1;
          unsigned int _next_fuel = f;
          List<unsigned int> _next_l2 = *(d_a10);
          List<unsigned int> _next_l1 = List<unsigned int>::nil();
          _loop_fuel = std::move(_next_fuel);
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
          continue;
        }
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(_loop_l1.v());
        if (std::holds_alternative<typename List<unsigned int>::Nil>(
                _loop_l2.v())) {
          auto _cell =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  typename List<std::pair<unsigned int, unsigned int>>::Cons(
                      std::make_pair(d_a0, default0), nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<
                   typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                   (*_write)->v_mut())
                   .d_a1;
          unsigned int _next_fuel = f;
          List<unsigned int> _next_l2 = List<unsigned int>::nil();
          List<unsigned int> _next_l1 = *(d_a1);
          _loop_fuel = std::move(_next_fuel);
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
          continue;
        } else {
          const auto &[d_a00, d_a10] =
              std::get<typename List<unsigned int>::Cons>(_loop_l2.v());
          auto _cell =
              std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
                  typename List<std::pair<unsigned int, unsigned int>>::Cons(
                      std::make_pair(d_a0, d_a00), nullptr));
          *(_write) = std::move(_cell);
          _write =
              &std::get<
                   typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                   (*_write)->v_mut())
                   .d_a1;
          unsigned int _next_fuel = f;
          List<unsigned int> _next_l2 = *(d_a10);
          List<unsigned int> _next_l1 = *(d_a1);
          _loop_fuel = std::move(_next_fuel);
          _loop_l2 = std::move(_next_l2);
          _loop_l1 = std::move(_next_l1);
          continue;
        }
      }
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) unsigned int
LoopifyGenerators::len_impl(const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {};

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = (_result + 1);
    }
  }
  return _result;
}

__attribute__((pure)) List<std::pair<unsigned int, unsigned int>>
LoopifyGenerators::zip_longest(const List<unsigned int> &l1,
                               const List<unsigned int> &l2,
                               const unsigned int &default0) {
  return zip_longest_aux(l1, l2, default0, (len_impl(l1) + len_impl(l2)));
}

/// build_list n builds tree-like list structure: build_list(4) -> 2,4,2.
__attribute__((pure)) List<unsigned int>
LoopifyGenerators::build_list_fuel(const unsigned int &fuel,
                                   const unsigned int &n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(16);
  _stack.emplace_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const unsigned int &n = _f.n;
      const unsigned int &fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int f = fuel - 1;
        if (n <= 0) {
          _result = List<unsigned int>::nil();
        } else {
          unsigned int n_ = n - 1;
          if (n_ <= 0) {
            _result = List<unsigned int>::cons(1u, List<unsigned int>::nil());
          } else {
            unsigned int _x = n_ - 1;
            unsigned int half = (2u ? n_ / 2u : 0);
            _stack.emplace_back(_Call1{n_});
            _stack.emplace_back(_Enter{half, f});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      unsigned int n_ = _f._s0;
      List<unsigned int> half_result = _result;
      _result = half_result.app(List<unsigned int>::cons(n_, half_result));
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifyGenerators::build_list(const unsigned int &n) {
  return build_list_fuel(100u, n);
}

/// take n l returns first n elements.
__attribute__((pure)) List<unsigned int>
LoopifyGenerators::take(const unsigned int &n, const List<unsigned int> &l) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  unsigned int _loop_n = n;
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      if (_loop_n == 0u) {
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
        const List<unsigned int> *_next_l = d_a1.get();
        unsigned int _next_n =
            (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
        _loop_l = _next_l;
        _loop_n = std::move(_next_n);
        continue;
      }
    }
  }
  return std::move(*(_head));
}

/// repeat x n creates list with n copies of x.
__attribute__((pure)) List<unsigned int>
LoopifyGenerators::repeat(unsigned int x, const unsigned int &n) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int m = _loop_n - 1;
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(x, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*(_head));
}

/// Helper: replicate single element n times.
__attribute__((pure)) List<unsigned int>
LoopifyGenerators::replicate_single(unsigned int x, const unsigned int &n) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int m = _loop_n - 1;
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(x, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*(_head));
}

/// replicate_each n l replicates each element n times: replicate_each 2 1,2 ->
/// 1,1,2,2.
__attribute__((pure)) List<unsigned int>
LoopifyGenerators::replicate_each(const unsigned int &n,
                                  const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    decltype(replicate_single(std::declval<unsigned int &>(),
                              std::declval<const unsigned int &>())) _s0;
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
      const List<unsigned int> &l = _f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        _stack.emplace_back(_Call1{replicate_single(d_a0, n)});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = _f._s0.app(_result);
    }
  }
  return _result;
}
