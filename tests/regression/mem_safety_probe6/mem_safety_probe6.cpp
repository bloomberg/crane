#include "mem_safety_probe6.h"

/// TEST 5: Chain of closures each pre-computing from the tail.
MemSafetyProbe6::mylist<std::function<uint64_t(uint64_t)>>
MemSafetyProbe6::build_chain(
    const MemSafetyProbe6::mylist<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe6::mylist<uint64_t> *l;
  };

  /// _Resume_Mycons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    std::function<uint64_t(uint64_t)> _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  MemSafetyProbe6::mylist<std::function<uint64_t(uint64_t)>> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified build_chain: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe6::mylist<uint64_t> &l = *_f.l;
      if (std::holds_alternative<
              typename MemSafetyProbe6::mylist<uint64_t>::Mynil>(l.v())) {
        _result = mylist<std::function<uint64_t(uint64_t)>>::mynil();
      } else {
        const auto &[a0, a1] =
            std::get<typename MemSafetyProbe6::mylist<uint64_t>::Mycons>(l.v());
        const MemSafetyProbe6::mylist<uint64_t> &a1_value = *a1;
        uint64_t rest_len = a1_value.length();
        _stack.emplace_back(_Resume_Mycons{
            [=](uint64_t n) mutable { return ((a0 + rest_len) + n); }});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = mylist<std::function<uint64_t(uint64_t)>>::mycons(
          std::move(_f._s0), std::move(_result));
    }
  }
  return _result;
}

uint64_t MemSafetyProbe6::apply_chain(
    const MemSafetyProbe6::mylist<std::function<uint64_t(uint64_t)>> &fns,
    uint64_t
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe6::mylist<std::function<uint64_t(uint64_t)>> *fns;
  };

  /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    std::function<uint64_t(uint64_t)> a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&fns});
  /// Loopified apply_chain: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe6::mylist<std::function<uint64_t(uint64_t)>> &fns =
          *_f.fns;
      if (std::holds_alternative<typename MemSafetyProbe6::mylist<
              std::function<uint64_t(uint64_t)>>::Mynil>(fns.v())) {
        _result = std::move(x);
      } else {
        const auto &[a0, a1] = std::get<typename MemSafetyProbe6::mylist<
            std::function<uint64_t(uint64_t)>>::Mycons>(fns.v());
        _stack.emplace_back(_Resume_Mycons{std::move(a0)});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = std::move(_f.a0)(std::move(_result));
    }
  }
  return _result;
}

/// TEST 6: Closure captures tail, then tail is used again
/// after the closure is created — tests double use.
uint64_t
MemSafetyProbe6::capture_and_reuse(uint64_t,
                                   const MemSafetyProbe6::mylist<uint64_t> &l) {
  if (std::holds_alternative<typename MemSafetyProbe6::mylist<uint64_t>::Mynil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename MemSafetyProbe6::mylist<uint64_t>::Mycons>(l.v());
    const MemSafetyProbe6::mylist<uint64_t> &a1_value = *a1;
    std::function<uint64_t(uint64_t)> f = [=](uint64_t n) mutable {
      return (a1_value.length() + n);
    };
    uint64_t tail_len = a1_value.length();
    return (f(a0) + tail_len);
  }
}
