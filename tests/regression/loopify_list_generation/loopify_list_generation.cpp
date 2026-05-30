#include "loopify_list_generation.h"

List<uint64_t> LoopifyListGeneration::replicate(
    uint64_t n,
    uint64_t
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_n_: saves [x], resumes after recursive call with _result.
  struct _Resume_n_ {
    uint64_t x;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified replicate: _Enter -> _Resume_n_.
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
        _stack.emplace_back(_Resume_n_{x});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = List<uint64_t>::cons(_f.x, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListGeneration::stutter(
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
  };

  /// _Resume_Cons: saves [a0_0, a0_1], resumes after recursive call with
  /// _result.
  struct _Resume_Cons {
    uint64_t a0_0;
    uint64_t a0_1;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified stutter: _Enter -> _Resume_Cons.
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
        _stack.emplace_back(_Resume_Cons{a0, a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(
          _f.a0_0, List<uint64_t>::cons(_f.a0_1, std::move(_result)));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListGeneration::cycle(
    uint64_t n,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_n_: saves [l], resumes after recursive call with _result.
  struct _Resume_n_ {
    List<uint64_t> l;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified cycle: _Enter -> _Resume_n_.
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
        _stack.emplace_back(_Resume_n_{l});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = std::move(_f.l).app(std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListGeneration::iterate(
    uint64_t n,
    uint64_t
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t x;
    uint64_t n;
  };

  /// _Resume_n_: saves [x], resumes after recursive call with _result.
  struct _Resume_n_ {
    uint64_t x;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{x, n});
  /// Loopified iterate: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t x = _f.x;
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_Resume_n_{x});
        _stack.emplace_back(_Enter{(x + UINT64_C(1)), n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = List<uint64_t>::cons(_f.x, std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListGeneration::replicate_list(
    const List<std::pair<uint64_t, uint64_t>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<std::pair<uint64_t, uint64_t>> *l;
  };

  /// _Resume_n: saves [_s0], resumes after recursive call with _result.
  struct _Resume_n {
    List<uint64_t> _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_n>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified replicate_list: _Enter -> _Resume_n.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<std::pair<uint64_t, uint64_t>> &l = *_f.l;
      if (std::holds_alternative<
              typename List<std::pair<uint64_t, uint64_t>>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(l.v());
        const uint64_t &n = a0.first;
        const uint64_t &x = a0.second;
        List<uint64_t> rep = replicate(n, x);
        _stack.emplace_back(_Resume_n{std::move(std::move(rep))});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n>(_frame));
      _result = std::move(_f._s0).app(std::move(_result));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListGeneration::repeat_with_sep(
    uint64_t sep, uint64_t n,
    uint64_t
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume__x: saves [x, sep], resumes after recursive call with _result.
  struct _Resume__x {
    uint64_t x;
    uint64_t sep;
  };

  using _Frame = std::variant<_Enter, _Resume__x>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified repeat_with_sep: _Enter -> _Resume__x.
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
        if (n_ <= 0) {
          _result = List<uint64_t>::cons(x, List<uint64_t>::nil());
        } else {
          uint64_t _x = n_ - 1;
          _stack.emplace_back(_Resume__x{x, sep});
          _stack.emplace_back(_Enter{n_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume__x>(_frame));
      _result = List<uint64_t>::cons(
          _f.x, List<uint64_t>::cons(_f.sep, std::move(_result)));
    }
  }
  return _result;
}

List<uint64_t> LoopifyListGeneration::range(
    uint64_t start,
    uint64_t
        len) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t len;
    uint64_t start;
  };

  /// _Resume_len_: saves [start], resumes after recursive call with _result.
  struct _Resume_len_ {
    uint64_t start;
  };

  using _Frame = std::variant<_Enter, _Resume_len_>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{len, start});
  /// Loopified range: _Enter -> _Resume_len_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t len = _f.len;
      uint64_t start = _f.start;
      if (len <= 0) {
        _result = List<uint64_t>::nil();
      } else {
        uint64_t len_ = len - 1;
        _stack.emplace_back(_Resume_len_{start});
        _stack.emplace_back(_Enter{len_, (start + UINT64_C(1))});
      }
    } else {
      auto _f = std::move(std::get<_Resume_len_>(_frame));
      _result = List<uint64_t>::cons(_f.start, std::move(_result));
    }
  }
  return _result;
}
