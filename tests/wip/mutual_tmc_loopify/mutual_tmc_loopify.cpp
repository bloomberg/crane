#include "mutual_tmc_loopify.h"

MutualTmcLoopify::mylist MutualTmcLoopify::evens(
    Nat n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    Nat n;
  };

  using _Frame = std::variant<_Enter>;
  MutualTmcLoopify::mylist _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{std::move(n)});
  /// Loopified evens: _Enter.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    auto _f = std::move(std::get<_Enter>(_frame));
    Nat n = std::move(_f.n);
    if (std::holds_alternative<typename Nat::O>(n.v_mut())) {
      _result = mylist::mnil();
    } else {
      auto &[a0] = std::get<typename Nat::S>(n.v_mut());
      _result = mylist::mcons(n, [](Nat _inl_n) -> MutualTmcLoopify::mylist {
        if (std::holds_alternative<typename Nat::O>(_inl_n.v_mut())) {
          return mylist::mnil();
        } else {
          auto &[_inl_a0] = std::get<typename Nat::S>(_inl_n.v_mut());
          return mylist::mcons(_inl_n, evens(*_inl_a0));
        }
      }(*a0));
    }
  }
  return _result;
}

MutualTmcLoopify::mylist MutualTmcLoopify::odds(Nat n) {
  if (std::holds_alternative<typename Nat::O>(n.v_mut())) {
    return mylist::mnil();
  } else {
    auto &[a0] = std::get<typename Nat::S>(n.v_mut());
    return mylist::mcons(n, evens(*a0));
  }
}

Nat MutualTmcLoopify::len(const MutualTmcLoopify::mylist &l) {
  if (std::holds_alternative<typename MutualTmcLoopify::mylist::Mnil>(l.v())) {
    return Nat::o();
  } else {
    const auto &[a0, a1] =
        std::get<typename MutualTmcLoopify::mylist::Mcons>(l.v());
    return Nat::s(len(*a1));
  }
}
