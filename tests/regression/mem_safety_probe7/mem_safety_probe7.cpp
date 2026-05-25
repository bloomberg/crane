#include "mem_safety_probe7.h"

uint64_t MemSafetyProbe7::sum_list(
    const MemSafetyProbe7::mylist<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe7::mylist<uint64_t> *l;
  };

  /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_list: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe7::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe7::mylist<uint64_t>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(l.v());
        _stack.emplace_back(_Resume_Mycons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.a0 + _result);
    }
  }
  return _result;
}

/// TEST 1: Build a list of closures where each captures the TAIL
/// and computes its length. The tail is unique_ptr.
MemSafetyProbe7::mylist<std::function<uint64_t(std::monostate)>>
MemSafetyProbe7::build_len_closures(
    const MemSafetyProbe7::mylist<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe7::mylist<uint64_t> *l;
  };

  /// _Resume_Mycons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    std::decay_t<decltype([=](std::monostate) mutable {
      return a1_value.length();
    })>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  MemSafetyProbe7::mylist<std::function<uint64_t(std::monostate)>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified build_len_closures: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe7::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe7::mylist<uint64_t>::Mynil>(l.v())) {
        _result = mylist<std::function<uint64_t(std::monostate)>>::mynil();
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(l.v());
        const MemSafetyProbe7::mylist<uint64_t> &a1_value = *a1;
        _stack.emplace_back(_Resume_Mycons{
            [=](std::monostate) mutable { return a1_value.length(); }});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = mylist<std::function<uint64_t(std::monostate)>>::mycons(
          _f._s0, _result);
    }
  }
  return _result;
}

uint64_t MemSafetyProbe7::sum_fns(
    const MemSafetyProbe7::mylist<std::function<uint64_t(std::monostate)>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe7::mylist<std::function<uint64_t(std::monostate)>> *l;
  };

  /// _Resume_Mycons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    uint64_t _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_fns: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe7::mylist<std::function<uint64_t(std::monostate)>>
          &l = *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe7::mylist<
              std::function<uint64_t(std::monostate)>>::Mynil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe7::mylist<
            std::function<uint64_t(std::monostate)>>::Mycons>(l.v());
        _stack.emplace_back(_Resume_Mycons{a0(std::monostate{})});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f._s0 + _result);
    }
  }
  return _result;
}

/// TEST 2: Build closures that compute the SUM of the tail.
/// Each closure captures the entire tail sublist.
MemSafetyProbe7::mylist<std::function<uint64_t(std::monostate)>>
MemSafetyProbe7::build_sum_closures(
    const MemSafetyProbe7::mylist<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe7::mylist<uint64_t> *l;
  };

  /// _Resume_Mycons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    std::decay_t<decltype([=](std::monostate) mutable {
      return sum_list(a1_value);
    })>
        _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  MemSafetyProbe7::mylist<std::function<uint64_t(std::monostate)>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified build_sum_closures: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe7::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe7::mylist<uint64_t>::Mynil>(l.v())) {
        _result = mylist<std::function<uint64_t(std::monostate)>>::mynil();
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(l.v());
        const MemSafetyProbe7::mylist<uint64_t> &a1_value = *a1;
        _stack.emplace_back(_Resume_Mycons{
            [=](std::monostate) mutable { return sum_list(a1_value); }});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = mylist<std::function<uint64_t(std::monostate)>>::mycons(
          _f._s0, _result);
    }
  }
  return _result;
}

/// TEST 4: Each closure captures the tail AND the current value.
/// After building all closures, call them — the captured lists
/// must be independent copies.
MemSafetyProbe7::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe7::build_accum_closures(
    const MemSafetyProbe7::mylist<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe7::mylist<uint64_t> *l;
  };

  /// _Resume_Mycons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    std::function<uint64_t(uint64_t)> _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  MemSafetyProbe7::mylist<std::function<uint64_t(uint64_t)>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified build_accum_closures: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe7::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe7::mylist<uint64_t>::Mynil>(l.v())) {
        _result = mylist<std::function<uint64_t(uint64_t)>>::mynil();
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(l.v());
        const MemSafetyProbe7::mylist<uint64_t> &a1_value = *a1;
        _stack.emplace_back(_Resume_Mycons{[=](uint64_t n) mutable {
          return ((a0 + sum_list(a1_value)) + n);
        }});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result =
          mylist<std::function<uint64_t(uint64_t)>>::mycons(_f._s0, _result);
    }
  }
  return _result;
}

uint64_t MemSafetyProbe7::apply_all(
    const MemSafetyProbe7::mylist<std::function<uint64_t(uint64_t)>> &l,
    uint64_t
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe7::mylist<std::function<uint64_t(uint64_t)>> *l;
  };

  /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    std::function<uint64_t(uint64_t)> a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified apply_all: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe7::mylist<std::function<uint64_t(uint64_t)>> &l =
          *_f.l;
      if (std::holds_alternative<typename MemSafetyProbe7::mylist<
              std::function<uint64_t(uint64_t)>>::Mynil>(l.v())) {
        _result = std::move(x);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe7::mylist<
            std::function<uint64_t(uint64_t)>>::Mycons>(l.v());
        _stack.emplace_back(_Resume_Mycons{std::move(a0)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = _f.a0(_result);
    }
  }
  return _result;
}

/// TEST 6: Stress test — large list, each closure captures
/// the entire remaining tail.
MemSafetyProbe7::mylist<uint64_t> MemSafetyProbe7::make_nat_list(
    uint64_t
        n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_n_: saves [n], resumes after recursive call with _result.
  struct _Resume_n_ {
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Resume_n_>;
  MemSafetyProbe7::mylist<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified make_nat_list: _Enter -> _Resume_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = mylist<uint64_t>::mynil();
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_Resume_n_{n});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Resume_n_>(_frame));
      _result = mylist<uint64_t>::mycons(_f.n, _result);
    }
  }
  return _result;
}
