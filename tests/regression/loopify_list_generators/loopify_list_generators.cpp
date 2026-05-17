#include "loopify_list_generators.h"

List<unsigned int> LoopifyListGenerators::cycle_fuel(
    unsigned int fuel, unsigned int n,
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    unsigned int n;
    unsigned int fuel;
  };

  /// _Resume_Cons: saves [l], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<unsigned int> l;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified cycle_fuel: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      unsigned int n = _f.n;
      unsigned int fuel = _f.fuel;
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
            _stack.emplace_back(_Resume_Cons{l});
            _stack.emplace_back(_Enter{n_, fuel_});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = _f.l.app(_result);
    }
  }
  return _result;
}

List<unsigned int> LoopifyListGenerators::cycle(unsigned int n,
                                                const List<unsigned int> &l) {
  return cycle_fuel((n * l.length()), n, l);
}

List<unsigned int> LoopifyListGenerators::range(unsigned int start,
                                                unsigned int count) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_count = std::move(count);
  unsigned int _loop_start = std::move(start);
  while (true) {
    if (_loop_count <= 0) {
      *_write = std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int count_ = _loop_count - 1;
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(_loop_start, nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      _loop_count = count_;
      _loop_start = (_loop_start + 1u);
      continue;
    }
  }
  return std::move(*_head);
}

List<unsigned int> LoopifyListGenerators::replicate_elem(unsigned int n,
                                                         unsigned int x) {
  std::unique_ptr<List<unsigned int>> _head{};
  std::unique_ptr<List<unsigned int>> *_write = &_head;
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_unique<List<unsigned int>>(List<unsigned int>::nil());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell = std::make_unique<List<unsigned int>>(
          typename List<unsigned int>::Cons(x, nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<unsigned int>::Cons>((*_write)->v_mut()).d_a1;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}

List<unsigned int> LoopifyListGenerators::replicate_each(
    unsigned int n,
    const List<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<unsigned int> *l;
  };

  /// _Resume_Cons: saves [reps], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<unsigned int> reps;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified replicate_each: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<unsigned int> &l = *_f.l;
      if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
        _result = List<unsigned int>::nil();
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<unsigned int>::Cons>(l.v());
        List<unsigned int> reps = replicate_elem(n, d_a0);
        _stack.emplace_back(_Resume_Cons{std::move(reps)});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = _f.reps.app(_result);
    }
  }
  return _result;
}

List<std::pair<unsigned int, unsigned int>>
LoopifyListGenerators::enumerate_aux(unsigned int idx,
                                     const List<unsigned int> &l) {
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::unique_ptr<List<std::pair<unsigned int, unsigned int>>> *_write = &_head;
  const List<unsigned int> *_loop_l = &l;
  unsigned int _loop_idx = std::move(idx);
  while (true) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            _loop_l->v())) {
      *_write = std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
          List<std::pair<unsigned int, unsigned int>>::nil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(_loop_l->v());
      auto _cell =
          std::make_unique<List<std::pair<unsigned int, unsigned int>>>(
              typename List<std::pair<unsigned int, unsigned int>>::Cons(
                  std::make_pair(_loop_idx, d_a0), nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
               (*_write)->v_mut())
               .d_a1;
      _loop_l = d_a1.get();
      _loop_idx = (_loop_idx + 1u);
      continue;
    }
  }
  return std::move(*_head);
}

List<std::pair<unsigned int, unsigned int>>
LoopifyListGenerators::enumerate(const List<unsigned int> &l) {
  return enumerate_aux(0u, l);
}
