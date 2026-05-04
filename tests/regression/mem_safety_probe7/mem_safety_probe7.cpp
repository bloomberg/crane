#include <mem_safety_probe7.h>

unsigned int MemSafetyProbe7::sum_list(
    const MemSafetyProbe7::mylist<unsigned int>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe7::mylist<unsigned int> *l;
  };

  /// _Resume_Mycons: saves [d_a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    unsigned int d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_list: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe7::mylist<unsigned int> &l = *(_f.l);
      if (std::holds_alternative<
              typename MemSafetyProbe7::mylist<unsigned int>::Mynil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename MemSafetyProbe7::mylist<unsigned int>::Mycons>(
                l.v());
        _stack.emplace_back(_Resume_Mycons{d_a0});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = (_f.d_a0 + _result);
    }
  }
  return _result;
}

/// TEST 1: Build a list of closures where each captures the TAIL
/// and computes its length. The tail is unique_ptr.
MemSafetyProbe7::mylist<std::function<unsigned int(std::monostate)>>
MemSafetyProbe7::build_len_closures(
    const MemSafetyProbe7::mylist<unsigned int> &l) {
  std::unique_ptr<
      MemSafetyProbe7::mylist<std::function<unsigned int(std::monostate)>>>
      _head{};
  std::unique_ptr<
      MemSafetyProbe7::mylist<std::function<unsigned int(std::monostate)>>>
      *_write = &_head;
  MemSafetyProbe7::mylist<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe7::mylist<unsigned int>::Mynil>(
            _loop_l.v())) {
      *(_write) = std::make_unique<
          MemSafetyProbe7::mylist<std::function<unsigned int(std::monostate)>>>(
          mylist<std::function<unsigned int(std::monostate)>>::mynil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename MemSafetyProbe7::mylist<unsigned int>::Mycons>(
              _loop_l.v());
      MemSafetyProbe7::mylist<unsigned int> d_a1_value = *(d_a1);
      auto _cell = std::make_unique<
          MemSafetyProbe7::mylist<std::function<unsigned int(std::monostate)>>>(
          typename mylist<std::function<unsigned int(std::monostate)>>::Mycons(
              [=](const std::monostate &) mutable {
                return d_a1_value.length();
              },
              nullptr));
      *(_write) = std::move(_cell);
      _write = &std::get<typename mylist<
          std::function<unsigned int(std::monostate)>>::Mycons>(
                    (*_write)->v_mut())
                    .d_a1;
      _loop_l = d_a1_value;
      continue;
    }
  }
  return std::move(*(_head));
}

unsigned int MemSafetyProbe7::sum_fns(
    const MemSafetyProbe7::mylist<std::function<unsigned int(std::monostate)>>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe7::mylist<std::function<unsigned int(std::monostate)>>
        *l;
  };

  /// _Resume_Mycons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_fns: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe7::mylist<std::function<unsigned int(std::monostate)>>
          &l = *(_f.l);
      if (std::holds_alternative<typename MemSafetyProbe7::mylist<
              std::function<unsigned int(std::monostate)>>::Mynil>(l.v())) {
        _result = 0u;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename MemSafetyProbe7::mylist<
            std::function<unsigned int(std::monostate)>>::Mycons>(l.v());
        _stack.emplace_back(_Resume_Mycons{d_a0(std::monostate{})});
        _stack.emplace_back(_Enter{d_a1.get()});
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
MemSafetyProbe7::mylist<std::function<unsigned int(std::monostate)>>
MemSafetyProbe7::build_sum_closures(
    const MemSafetyProbe7::mylist<unsigned int> &l) {
  std::unique_ptr<
      MemSafetyProbe7::mylist<std::function<unsigned int(std::monostate)>>>
      _head{};
  std::unique_ptr<
      MemSafetyProbe7::mylist<std::function<unsigned int(std::monostate)>>>
      *_write = &_head;
  MemSafetyProbe7::mylist<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe7::mylist<unsigned int>::Mynil>(
            _loop_l.v())) {
      *(_write) = std::make_unique<
          MemSafetyProbe7::mylist<std::function<unsigned int(std::monostate)>>>(
          mylist<std::function<unsigned int(std::monostate)>>::mynil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename MemSafetyProbe7::mylist<unsigned int>::Mycons>(
              _loop_l.v());
      MemSafetyProbe7::mylist<unsigned int> d_a1_value = *(d_a1);
      auto _cell = std::make_unique<
          MemSafetyProbe7::mylist<std::function<unsigned int(std::monostate)>>>(
          typename mylist<std::function<unsigned int(std::monostate)>>::Mycons(
              [=](const std::monostate &) mutable {
                return sum_list(d_a1_value);
              },
              nullptr));
      *(_write) = std::move(_cell);
      _write = &std::get<typename mylist<
          std::function<unsigned int(std::monostate)>>::Mycons>(
                    (*_write)->v_mut())
                    .d_a1;
      _loop_l = d_a1_value;
      continue;
    }
  }
  return std::move(*(_head));
}

/// TEST 4: Each closure captures the tail AND the current value.
/// After building all closures, call them — the captured lists
/// must be independent copies.
MemSafetyProbe7::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe7::build_accum_closures(
    const MemSafetyProbe7::mylist<unsigned int> &l) {
  std::unique_ptr<
      MemSafetyProbe7::mylist<std::function<unsigned int(unsigned int)>>>
      _head{};
  std::unique_ptr<
      MemSafetyProbe7::mylist<std::function<unsigned int(unsigned int)>>>
      *_write = &_head;
  MemSafetyProbe7::mylist<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe7::mylist<unsigned int>::Mynil>(
            _loop_l.v())) {
      *(_write) = std::make_unique<
          MemSafetyProbe7::mylist<std::function<unsigned int(unsigned int)>>>(
          mylist<std::function<unsigned int(unsigned int)>>::mynil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename MemSafetyProbe7::mylist<unsigned int>::Mycons>(
              _loop_l.v());
      MemSafetyProbe7::mylist<unsigned int> d_a1_value = *(d_a1);
      auto _cell = std::make_unique<
          MemSafetyProbe7::mylist<std::function<unsigned int(unsigned int)>>>(
          typename mylist<std::function<unsigned int(unsigned int)>>::Mycons(
              [=](const unsigned int n) mutable {
                return ((d_a0 + sum_list(d_a1_value)) + n);
              },
              nullptr));
      *(_write) = std::move(_cell);
      _write = &std::get<typename mylist<
          std::function<unsigned int(unsigned int)>>::Mycons>(
                    (*_write)->v_mut())
                    .d_a1;
      _loop_l = d_a1_value;
      continue;
    }
  }
  return std::move(*(_head));
}

unsigned int MemSafetyProbe7::apply_all(
    const MemSafetyProbe7::mylist<std::function<unsigned int(unsigned int)>> &l,
    const unsigned int
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe7::mylist<std::function<unsigned int(unsigned int)>> *l;
  };

  /// _Resume_Mycons: saves [d_a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    std::function<unsigned int(unsigned int)> d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified apply_all: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe7::mylist<std::function<unsigned int(unsigned int)>>
          &l = *(_f.l);
      if (std::holds_alternative<typename MemSafetyProbe7::mylist<
              std::function<unsigned int(unsigned int)>>::Mynil>(l.v())) {
        _result = x;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename MemSafetyProbe7::mylist<
            std::function<unsigned int(unsigned int)>>::Mycons>(l.v());
        _stack.emplace_back(_Resume_Mycons{std::move(d_a0)});
        _stack.emplace_back(_Enter{d_a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = _f.d_a0(_result);
    }
  }
  return _result;
}

/// TEST 6: Stress test — large list, each closure captures
/// the entire remaining tail.
MemSafetyProbe7::mylist<unsigned int>
MemSafetyProbe7::make_nat_list(const unsigned int n) {
  std::unique_ptr<MemSafetyProbe7::mylist<unsigned int>> _head{};
  std::unique_ptr<MemSafetyProbe7::mylist<unsigned int>> *_write = &_head;
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      *(_write) = std::make_unique<MemSafetyProbe7::mylist<unsigned int>>(
          mylist<unsigned int>::mynil());
      break;
    } else {
      unsigned int n_ = _loop_n - 1;
      auto _cell = std::make_unique<MemSafetyProbe7::mylist<unsigned int>>(
          typename mylist<unsigned int>::Mycons(_loop_n, nullptr));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename mylist<unsigned int>::Mycons>((*_write)->v_mut())
               .d_a1;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*(_head));
}
