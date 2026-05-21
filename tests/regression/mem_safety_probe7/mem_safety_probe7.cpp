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
    const MemSafetyProbe7::mylist<uint64_t> &l) {
  std::shared_ptr<
      MemSafetyProbe7::mylist<std::function<uint64_t(std::monostate)>>>
      _head{};
  std::shared_ptr<
      MemSafetyProbe7::mylist<std::function<uint64_t(std::monostate)>>>
      *_write = &_head;
  MemSafetyProbe7::mylist<uint64_t> _loop_l = l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe7::mylist<uint64_t>::Mynil>(_loop_l.v())) {
      *_write = std::make_shared<
          MemSafetyProbe7::mylist<std::function<uint64_t(std::monostate)>>>(
          mylist<std::function<uint64_t(std::monostate)>>::mynil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(
              _loop_l.v());
      const MemSafetyProbe7::mylist<uint64_t> &a1_value = *a1;
      auto _cell = std::make_shared<
          MemSafetyProbe7::mylist<std::function<uint64_t(std::monostate)>>>(
          typename mylist<std::function<uint64_t(std::monostate)>>::Mycons(
              [=](std::monostate) mutable { return a1_value.length(); },
              nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename mylist<
          std::function<uint64_t(std::monostate)>>::Mycons>((*_write)->v_mut())
                    .a1;
      _loop_l = a1_value;
      continue;
    }
  }
  return std::move(*_head);
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
    const MemSafetyProbe7::mylist<uint64_t> &l) {
  std::shared_ptr<
      MemSafetyProbe7::mylist<std::function<uint64_t(std::monostate)>>>
      _head{};
  std::shared_ptr<
      MemSafetyProbe7::mylist<std::function<uint64_t(std::monostate)>>>
      *_write = &_head;
  MemSafetyProbe7::mylist<uint64_t> _loop_l = l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe7::mylist<uint64_t>::Mynil>(_loop_l.v())) {
      *_write = std::make_shared<
          MemSafetyProbe7::mylist<std::function<uint64_t(std::monostate)>>>(
          mylist<std::function<uint64_t(std::monostate)>>::mynil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(
              _loop_l.v());
      const MemSafetyProbe7::mylist<uint64_t> &a1_value = *a1;
      auto _cell = std::make_shared<
          MemSafetyProbe7::mylist<std::function<uint64_t(std::monostate)>>>(
          typename mylist<std::function<uint64_t(std::monostate)>>::Mycons(
              [=](std::monostate) mutable { return sum_list(a1_value); },
              nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename mylist<
          std::function<uint64_t(std::monostate)>>::Mycons>((*_write)->v_mut())
                    .a1;
      _loop_l = a1_value;
      continue;
    }
  }
  return std::move(*_head);
}

/// TEST 4: Each closure captures the tail AND the current value.
/// After building all closures, call them — the captured lists
/// must be independent copies.
MemSafetyProbe7::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe7::build_accum_closures(
    const MemSafetyProbe7::mylist<uint64_t> &l) {
  std::shared_ptr<MemSafetyProbe7::mylist<std::function<uint64_t(uint64_t)>>>
      _head{};
  std::shared_ptr<MemSafetyProbe7::mylist<std::function<uint64_t(uint64_t)>>>
      *_write = &_head;
  MemSafetyProbe7::mylist<uint64_t> _loop_l = l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe7::mylist<uint64_t>::Mynil>(_loop_l.v())) {
      *_write = std::make_shared<
          MemSafetyProbe7::mylist<std::function<uint64_t(uint64_t)>>>(
          mylist<std::function<uint64_t(uint64_t)>>::mynil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename MemSafetyProbe7::mylist<uint64_t>::Mycons>(
              _loop_l.v());
      const MemSafetyProbe7::mylist<uint64_t> &a1_value = *a1;
      auto _cell = std::make_shared<
          MemSafetyProbe7::mylist<std::function<uint64_t(uint64_t)>>>(
          typename mylist<std::function<uint64_t(uint64_t)>>::Mycons(
              [=](uint64_t n) mutable {
                return ((a0 + sum_list(a1_value)) + n);
              },
              nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename mylist<std::function<uint64_t(uint64_t)>>::Mycons>(
               (*_write)->v_mut())
               .a1;
      _loop_l = a1_value;
      continue;
    }
  }
  return std::move(*_head);
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
MemSafetyProbe7::mylist<uint64_t> MemSafetyProbe7::make_nat_list(uint64_t n) {
  std::shared_ptr<MemSafetyProbe7::mylist<uint64_t>> _head{};
  std::shared_ptr<MemSafetyProbe7::mylist<uint64_t>> *_write = &_head;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *_write = std::make_shared<MemSafetyProbe7::mylist<uint64_t>>(
          mylist<uint64_t>::mynil());
      break;
    } else {
      uint64_t n_ = _loop_n - 1;
      auto _cell = std::make_shared<MemSafetyProbe7::mylist<uint64_t>>(
          typename mylist<uint64_t>::Mycons(_loop_n, nullptr));
      *_write = std::move(_cell);
      _write =
          &std::get<typename mylist<uint64_t>::Mycons>((*_write)->v_mut()).a1;
      _loop_n = n_;
      continue;
    }
  }
  return std::move(*_head);
}
