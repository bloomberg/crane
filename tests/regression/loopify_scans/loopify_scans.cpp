#include "loopify_scans.h"

List<uint64_t> LoopifyScans::scanl(
    uint64_t acc,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t acc;
  };

  /// _Resume_Cons: saves [acc], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t acc;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, acc});
  /// Loopified scanl: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t acc = _f.acc;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::cons(acc, List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{acc});
        _stack.emplace_back(_Enter{a1.get(), (acc + a0)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f.acc, _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyScans::scanl_mult(
    uint64_t acc,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t acc;
  };

  /// _Resume_Cons: saves [acc], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t acc;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, acc});
  /// Loopified scanl_mult: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t acc = _f.acc;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::cons(acc, List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{acc});
        _stack.emplace_back(_Enter{a1.get(), (acc * a0)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f.acc, _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyScans::running_max(
    uint64_t current,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t current;
  };

  /// _Resume_Cons: saves [current], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t current;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, current});
  /// Loopified running_max: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t current = _f.current;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::cons(current, List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        uint64_t new_max;
        if (current < a0) {
          new_max = a0;
        } else {
          new_max = current;
        }
        _stack.emplace_back(_Resume_Cons{current});
        _stack.emplace_back(_Enter{a1.get(), new_max});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f.current, _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyScans::running_min(
    uint64_t current,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t current;
  };

  /// _Resume_Cons: saves [current], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t current;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, current});
  /// Loopified running_min: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t current = _f.current;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::cons(current, List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        uint64_t new_min;
        if (a0 < current) {
          new_min = a0;
        } else {
          new_min = current;
        }
        _stack.emplace_back(_Resume_Cons{current});
        _stack.emplace_back(_Enter{a1.get(), new_min});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f.current, _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyScans::pairwise_diff(
    uint64_t prev,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t prev;
  };

  /// _Resume_Cons: saves [diff], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t diff;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, prev});
  /// Loopified pairwise_diff: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t prev = _f.prev;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        uint64_t diff;
        if (a0 < prev) {
          uint64_t sub = (((prev - a0) > prev ? 0 : (prev - a0)));
          if (prev < sub) {
            diff = UINT64_C(0);
          } else {
            diff = sub;
          }
        } else {
          uint64_t sub = (((a0 - prev) > a0 ? 0 : (a0 - prev)));
          if (a0 < sub) {
            diff = UINT64_C(0);
          } else {
            diff = sub;
          }
        }
        _stack.emplace_back(_Resume_Cons{diff});
        _stack.emplace_back(_Enter{a1.get(), a0});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = List<uint64_t>::cons(_f.diff, _result);
    }
  }
  return _result;
}

List<uint64_t> LoopifyScans::accumulate_if_even(
    uint64_t acc,
    const List<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<uint64_t> *l;
    uint64_t acc;
  };

  /// _Resume1: saves [acc], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t acc;
  };

  /// _Resume2: saves [acc], resumes after recursive call with _result.
  struct _Resume2 {
    uint64_t acc;
  };

  using _Frame = std::variant<_Enter, _Resume1, _Resume2>;
  List<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, acc});
  /// Loopified accumulate_if_even: _Enter -> _Resume1 -> _Resume2.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<uint64_t> &l = *_f.l;
      uint64_t acc = _f.acc;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<uint64_t>::cons(acc, List<uint64_t>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        if ((UINT64_C(2) ? a0 % UINT64_C(2) : a0) == UINT64_C(0)) {
          _stack.emplace_back(_Resume1{acc});
          _stack.emplace_back(_Enter{a1.get(), (acc + a0)});
        } else {
          _stack.emplace_back(_Resume2{acc});
          _stack.emplace_back(_Enter{a1.get(), acc});
        }
      }
    } else if (std::holds_alternative<_Resume1>(_frame)) {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.acc, _result);
    } else {
      auto _f = std::move(std::get<_Resume2>(_frame));
      _result = List<uint64_t>::cons(_f.acc, _result);
    }
  }
  return _result;
}
