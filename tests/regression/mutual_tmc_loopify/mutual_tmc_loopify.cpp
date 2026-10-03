#include "mutual_tmc_loopify.h"

MutualTmcLoopify::mylist MutualTmcLoopify::evens(
    const Nat
        &n) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    Nat n;
  };

  /// _Enter_inl: captures varying parameters for each recursive call.
  struct _Enter_inl {
    Nat _inl_n;
  };

  /// _Cont_S: saves [n], resumes after recursive call, then processes rest.
  struct _Cont_S {
    Nat n;
  };

  /// _Cont_S_1: saves [_inl_n], resumes after recursive call, then processes
  /// rest.
  struct _Cont_S_1 {
    Nat _inl_n;
  };

  using _Frame = std::variant<_Enter, _Enter_inl, _Cont_S, _Cont_S_1>;
  MutualTmcLoopify::mylist _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified evens: _Enter -> _Cont_S -> _Cont_S_1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const Nat &n = std::move(_f.n);
      if (std::holds_alternative<typename Nat::O>(n.v())) {
        _result = mylist::mnil();
      } else {
        const auto &[a0] = std::get<typename Nat::S>(n.v());
        _stack.emplace_back(_Cont_S{n});
        _stack.emplace_back(_Enter_inl{*a0});
      }
    } else if (std::holds_alternative<_Enter_inl>(_frame)) {
      auto _f = std::move(std::get<_Enter_inl>(_frame));
      const Nat &_inl_n = std::move(_f._inl_n);
      if (std::holds_alternative<typename Nat::O>(_inl_n.v())) {
        _result = mylist::mnil();
      } else {
        const auto &[_inl_a0] = std::get<typename Nat::S>(_inl_n.v());
        _stack.emplace_back(_Cont_S_1{_inl_n});
        _stack.emplace_back(_Enter{*_inl_a0});
      }
    } else if (std::holds_alternative<_Cont_S>(_frame)) {
      auto _f = std::move(std::get<_Cont_S>(_frame));
      const Nat &n = std::move(_f.n);
      _result = mylist::mcons(n, std::move(_result));
    } else {
      auto _f = std::move(std::get<_Cont_S_1>(_frame));
      const Nat &_inl_n = std::move(_f._inl_n);
      MutualTmcLoopify::mylist _inl__tmp1 = std::move(_result);
      _result = mylist::mcons(_inl_n, std::move(_inl__tmp1));
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
    const auto &[a0, a1] =
        std::get<typename MutualTmcLoopify::mylist::Mcons>(l.v());
    return Nat::s(len(*a1));
  }
}
