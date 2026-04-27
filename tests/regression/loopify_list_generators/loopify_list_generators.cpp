#include <loopify_list_generators.h>

__attribute__((pure)) List<unsigned int>
LoopifyListGenerators::cycle_fuel(const unsigned int &fuel,
                                  const unsigned int &n,
                                  const List<unsigned int> &l) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    const List<unsigned int> _s0;
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
      const unsigned int n = _f.n;
      const unsigned int fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<unsigned int>::nil();
      } else {
        unsigned int fuel_ = fuel - 1;
        if (n <= 0) {
          _result = List<unsigned int>::nil();
        } else {
          unsigned int n_ = n - 1;
          if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
            _result = List<unsigned int>::nil();
          } else {
            _stack.emplace_back(_Call1{l});
            _stack.emplace_back(_Enter{n_, fuel_});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = _f._s0.app(_result);
    }
  }
  return _result;
}

__attribute__((pure)) List<unsigned int>
LoopifyListGenerators::cycle(const unsigned int &n,
                             const List<unsigned int> &l) {
  return cycle_fuel((n * l.length()), n, l);
}

__attribute__((pure)) List<unsigned int>
LoopifyListGenerators::range(unsigned int start, const unsigned int &count) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_count = count;
  unsigned int _loop_start = std::move(start);
  while (true) {
    if (_loop_count <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int count_ = _loop_count - 1;
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(_loop_start, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      unsigned int _next_count = count_;
      unsigned int _next_start = (_loop_start + 1u);
      _loop_count = std::move(_next_count);
      _loop_start = std::move(_next_start);
      continue;
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyListGenerators::replicate_elem(const unsigned int &n, unsigned int x) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) =
          std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(x, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<unsigned int>
LoopifyListGenerators::replicate_each(const unsigned int &n,
                                      const List<unsigned int> &l) {
  struct _Enter {
    const List<unsigned int> l;
  };

  struct _Call1 {
    List<unsigned int> _s0;
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
        List<unsigned int> reps = replicate_elem(n, d_a0);
        _stack.emplace_back(_Call1{reps});
        _stack.emplace_back(_Enter{*(d_a1)});
      }
    } else {
      auto _f = std::move(std::get<_Call1>(_frame));
      _result = _f._s0.app(_result);
    }
  }
  return _result;
}

__attribute__((pure)) List<std::pair<unsigned int, unsigned int>>
LoopifyListGenerators::enumerate_aux(unsigned int idx,
                                     const List<unsigned int> &l) {
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> *_write = &_head;
  List<unsigned int> _loop_l = l;
  unsigned int _loop_idx = std::move(idx);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_loop_l.v())) {
      *(_write) = std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
          List<std::pair<unsigned int, unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l.v());
      auto _cell =
          std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
              typename List<std::pair<unsigned int, unsigned int>>::Cons(
                  std::make_pair(_loop_idx, d_a0), nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
               (*_write)->v_mut())
               .d_a1;
      List<unsigned int> _next_l = *(d_a1);
      unsigned int _next_idx = (_loop_idx + 1u);
      _loop_l = std::move(_next_l);
      _loop_idx = std::move(_next_idx);
      continue;
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) List<std::pair<unsigned int, unsigned int>>
LoopifyListGenerators::enumerate(const List<unsigned int> &l) {
  return enumerate_aux(0u, l);
}
