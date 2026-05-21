#include "loopify_list_generators.h"

List<uint64_t> LoopifyListGenerators::cycle_fuel(
    uint64_t fuel, uint64_t n,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Resume_Cons: saves [l], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> l;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n, fuel});
  /// Loopified cycle_fuel: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t fuel_ = fuel - 1;
        if (n <= 0) {
          _result = List<uint64_t>::nil();
        } else {
          uint64_t n_ = n - 1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
            _result = List<uint64_t>::nil();
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

List<uint64_t> LoopifyListGenerators::cycle(uint64_t n,
                                            const List<uint64_t> &l) {
  return cycle_fuel((n * l.length()), n, l);
}

List<uint64_t> LoopifyListGenerators::range(uint64_t start, uint64_t count) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_count = std::move(count);
  uint64_t _loop_start = std::move(start);
  while (true) {
    if (_loop_count <= 0) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t count_ = _loop_count - 1;
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(_loop_start, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_count = count_;
      _loop_start = (_loop_start + UINT64_C(1));
      continue;
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyListGenerators::replicate_elem(uint64_t n, uint64_t x) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(x, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}

List<uint64_t> LoopifyListGenerators::replicate_each(
    uint64_t n,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [reps], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> reps;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified replicate_each: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        List<uint64_t> reps = replicate_elem(n, a0);
        _stack.emplace_back(_Resume_Cons{std::move(reps)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = _f.reps.app(_result);
    }
  }
  return _result;
}

List<std::pair<uint64_t, uint64_t>>
LoopifyListGenerators::enumerate_aux(uint64_t idx, const List<uint64_t> &l) {
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> _head{};
  std::shared_ptr<List<std::pair<uint64_t, uint64_t>>> *_write = &_head;
  const List<uint64_t> *_loop_l = &l;
  uint64_t _loop_idx = std::move(idx);
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
      *_write = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
          List<std::pair<uint64_t, uint64_t>>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_l->v());
      auto _cell = std::make_shared<List<std::pair<uint64_t, uint64_t>>>(
          typename List<std::pair<uint64_t, uint64_t>>::Cons(
              std::make_pair(_loop_idx, a0), nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(
                    (*_write)->v_mut())
                    .l;
      _loop_l = a1.get();
      _loop_idx = (_loop_idx + UINT64_C(1));
      continue;
    }
  }
  return std::move(*_head);
}

List<std::pair<uint64_t, uint64_t>>
LoopifyListGenerators::enumerate(const List<uint64_t> &l) {
  return enumerate_aux(UINT64_C(0), l);
}
