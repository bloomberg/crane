#include "loopify_list_generators.h"

List<uint64_t> LoopifyListGenerators::cycle_fuel(
    uint64_t fuel, uint64_t n,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
    uint64_t fuel;
  };

  /// _Resume_Cons: resumes after recursive call with _result.
  struct _Resume_Cons {};

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
            _stack.emplace_back(_Resume_Cons{});
            _stack.emplace_back(_Enter{n_, fuel_});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = l.app(std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListGenerators::cycle(uint64_t n,
                                            const List<uint64_t> &l) {
  return cycle_fuel((n * l.length()), n, l);
}

List<uint64_t> LoopifyListGenerators::range(
    uint64_t start,
    uint64_t count) { /// _Enter: captures varying parameters for each recursive
                      /// call.

  struct _Enter {
    uint64_t count;
    uint64_t start;
  };

  /// _Resume_count_: saves [start], resumes after recursive call with _result.
  struct _Resume_count_ {
    uint64_t start;
  };

  using _Frame = std::variant<_Enter, _Resume_count_>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{count, start});
  /// Loopified range: _Enter -> _Resume_count_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t count = _f.count;
      uint64_t start = _f.start;
      if (count <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t count_ = count - 1;
        _stack.emplace_back(_Resume_count_{start});
        _stack.emplace_back(_Enter{count_, (start + UINT64_C(1))});
      }
    } else {
      auto _f = std::move(std::get<_Resume_count_>(_frame));
      _result = List<uint64_t>::cons(_f.start, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListGenerators::replicate_elem(
    uint64_t n,
    uint64_t
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_n_: resumes after recursive call with _result.
  struct _Resume_n_ {};

  using _Frame = std::variant<_Enter, _Resume_n_>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified replicate_elem: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_Resume_n_{});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = List<uint64_t>::cons(x, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListGenerators::replicate_each(
    uint64_t n,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    List<uint64_t> _s0;
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
        _stack.emplace_back(_Resume_Cons{std::move(std::move(reps))});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = std::move(_f._s0).app(std::move(_result));
    }
  }
  return _result;
}

List<std::pair<uint64_t, uint64_t>> LoopifyListGenerators::enumerate_aux(
    uint64_t idx,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t idx;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    std::decay_t<decltype(std::make_pair(std::declval<uint64_t &>(),
                                         std::declval<uint64_t &>()))>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<std::pair<uint64_t, uint64_t>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, idx});
  /// Loopified enumerate_aux: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t idx = _f.idx;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<std::pair<uint64_t, uint64_t>>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{std::make_pair(idx, a0)});
        _stack.emplace_back(_Enter{a1.get(), (idx + UINT64_C(1))});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result =
          List<std::pair<uint64_t, uint64_t>>::cons(_f._s0, std::move(_result));
    }
  }
  return _result;
}

List<std::pair<uint64_t, uint64_t>>
LoopifyListGenerators::enumerate(const List<uint64_t> &l) {
  return enumerate_aux(UINT64_C(0), l);
}
