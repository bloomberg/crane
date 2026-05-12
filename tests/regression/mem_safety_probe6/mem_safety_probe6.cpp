#include "mem_safety_probe6.h"

/// TEST 5: Chain of closures each pre-computing from the tail.
MemSafetyProbe6::mylist<std::function<unsigned int(unsigned int)>>
MemSafetyProbe6::build_chain(const MemSafetyProbe6::mylist<unsigned int> &l) {
  std::unique_ptr<
      MemSafetyProbe6::mylist<std::function<unsigned int(unsigned int)>>>
      _head{};
  std::unique_ptr<
      MemSafetyProbe6::mylist<std::function<unsigned int(unsigned int)>>>
      *_write = &_head;
  MemSafetyProbe6::mylist<unsigned int> _loop_l = l;
  while (true) {
    if (std::holds_alternative<
            typename MemSafetyProbe6::mylist<unsigned int>::Mynil>(
            _loop_l.v())) {
      *(_write) = std::make_unique<
          MemSafetyProbe6::mylist<std::function<unsigned int(unsigned int)>>>(
          mylist<std::function<unsigned int(unsigned int)>>::mynil());
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename MemSafetyProbe6::mylist<unsigned int>::Mycons>(
              _loop_l.v());
      MemSafetyProbe6::mylist<unsigned int> d_a1_value = *(d_a1);
      unsigned int rest_len = d_a1_value.length();
      auto _cell = std::make_unique<
          MemSafetyProbe6::mylist<std::function<unsigned int(unsigned int)>>>(
          typename mylist<std::function<unsigned int(unsigned int)>>::Mycons(
              [=](const unsigned int n) mutable {
                return ((d_a0 + rest_len) + n);
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

unsigned int MemSafetyProbe6::apply_chain(
    const MemSafetyProbe6::mylist<std::function<unsigned int(unsigned int)>>
        &fns,
    const unsigned int
        x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const MemSafetyProbe6::mylist<std::function<unsigned int(unsigned int)>>
        *fns;
  };

  /// _Resume_Mycons: saves [d_a0], resumes after recursive call with _result.
  struct _Resume_Mycons {
    std::function<unsigned int(unsigned int)> d_a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Mycons>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter(&fns));
  /// Loopified apply_chain: _Enter -> _Resume_Mycons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const MemSafetyProbe6::mylist<std::function<unsigned int(unsigned int)>>
          &fns = *(_f.fns);
      if (std::holds_alternative<typename MemSafetyProbe6::mylist<
              std::function<unsigned int(unsigned int)>>::Mynil>(fns.v())) {
        _result = x;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename MemSafetyProbe6::mylist<
            std::function<unsigned int(unsigned int)>>::Mycons>(fns.v());
        _stack.emplace_back(_Resume_Mycons(std::move(d_a0)));
        _stack.emplace_back(_Enter(d_a1.get()));
      }
    } else {
      auto _f = std::move(std::get<_Resume_Mycons>(_frame));
      _result = _f.d_a0(_result);
    }
  }
  return _result;
}

/// TEST 6: Closure captures tail, then tail is used again
/// after the closure is created — tests double use.
unsigned int MemSafetyProbe6::capture_and_reuse(
    const unsigned int, const MemSafetyProbe6::mylist<unsigned int> &l) {
  if (std::holds_alternative<
          typename MemSafetyProbe6::mylist<unsigned int>::Mynil>(l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename MemSafetyProbe6::mylist<unsigned int>::Mycons>(l.v());
    MemSafetyProbe6::mylist<unsigned int> d_a1_value = *(d_a1);
    std::function<unsigned int(unsigned int)> f =
        [=](const unsigned int n) mutable { return (d_a1_value.length() + n); };
    unsigned int tail_len = d_a1_value.length();
    return (f(d_a0) + tail_len);
  }
}
