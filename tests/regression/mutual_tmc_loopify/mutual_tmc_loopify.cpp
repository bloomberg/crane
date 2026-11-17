#include "mutual_tmc_loopify.h"

MutualTmcLoopify::mylist MutualTmcLoopify::evens(const Nat &n) {
  // Explicit stack replaces the non-tail recursion of evens: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const Nat *n;
  };

  struct _call_odds_entry {
    const Nat *n0;
  };

  struct _after_evens_in_S {
    Nat n0;
  };

  struct _after_odds_entry_in_S {
    Nat n;
  };

  using _frame = std::variant<_call, _call_odds_entry, _after_evens_in_S,
                              _after_odds_entry_in_S>;
  MutualTmcLoopify::mylist _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&n});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const Nat &n = *_f.n;
      if (std::holds_alternative<typename Nat::O>(n.v())) {
        _result = mylist::mnil();
      } else {
        const auto &[a00] = std::get<typename Nat::S>(n.v());
        _stack.emplace_back(_after_odds_entry_in_S{n});
        _stack.emplace_back(_call_odds_entry{crane_raw(a00)});
      }
    } else if (std::holds_alternative<_call_odds_entry>(_popped)) {
      auto _f = std::move(std::get<_call_odds_entry>(_popped));
      const Nat &n0 = *_f.n0;
      if (std::holds_alternative<typename Nat::O>(n0.v())) {
        _result = mylist::mnil();
      } else {
        const auto &[a0] = std::get<typename Nat::S>(n0.v());
        _stack.emplace_back(_after_evens_in_S{n0});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_evens_in_S>(_popped)) {
      auto _f = std::move(std::get<_after_evens_in_S>(_popped));
      Nat n0 = std::move(_f.n0);
      _result = mylist::mcons(std::move(n0), std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_odds_entry_in_S>(_popped));
      Nat n = std::move(_f.n);
      _result = mylist::mcons(std::move(n), std::move(_result));
    }
  }
  return _result;
}

MutualTmcLoopify::mylist MutualTmcLoopify::odds(const Nat &n) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    return mylist::mnil();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    return mylist::mcons(n, evens(*a0));
  }
}

Nat MutualTmcLoopify::len(const MutualTmcLoopify::mylist &l) {
  if (std::holds_alternative<typename MutualTmcLoopify::mylist::Mnil>(l.v())) {
    return Nat::o();
  } else {
    const auto &[_, a1] =
        std::get<typename MutualTmcLoopify::mylist::Mcons>(l.v());
    return Nat::s(len(*a1));
  }
}
