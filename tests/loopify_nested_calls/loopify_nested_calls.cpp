#include "loopify_nested_calls.h"

uint64_t sum_signum(uint64_t n) { /// _Enter: captures varying parameters for
                                  /// each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Cont_n_: saves [n_], resumes after recursive call, then processes rest.
  struct _Cont_n_ {
    uint64_t n_;
  };

  using _Frame = std::variant<_Enter, _Cont_n_>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified sum_signum: _Enter -> _Cont_n_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t n_ = n - 1;
        _stack.emplace_back(_Cont_n_{n_});
        _stack.emplace_back(_Enter{n_});
      }
    } else {
      auto _f = std::move(std::get<_Cont_n_>(_frame));
      uint64_t n_ = _f.n_;
      uint64_t rest = std::move(_result);
      uint64_t here;
      if (n_ == UINT64_C(0)) {
        here = UINT64_C(0);
      } else {
        here = UINT64_C(1);
      }
      _result = (rest + here);
    }
  }
  return _result;
}

List<uint64_t> down_let(uint64_t n) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Cont1: saves [n_], resumes after recursive call, then processes rest.
  struct _Cont1 {
    uint64_t n_;
  };

  using _Frame = std::variant<_Enter, _Cont1>;
  List<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified down_let: _Enter -> _Cont1.
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
        List<uint64_t> rest;
        if (n_ == UINT64_C(0)) {
          rest = List<uint64_t>::nil();
          {
            _result = List<uint64_t>::cons(n_, std::move(rest));
          }
        } else {
          _stack.emplace_back(_Cont1{n_});
          _stack.emplace_back(_Enter{n_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Cont1>(_frame));
      uint64_t n_ = _f.n_;
      auto rest = std::move(_result);
      _result = List<uint64_t>::cons(n_, std::move(rest));
    }
  }
  return _result;
}

List<uint64_t> down_inline(uint64_t n) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume1: saves [n_], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t n_;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  List<uint64_t> _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified down_inline: _Enter -> _Resume1.
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
        if (n_ == UINT64_C(0)) {
          _result = List<uint64_t>::cons(n_, List<uint64_t>::nil());
        } else {
          _stack.emplace_back(_Resume1{n_});
          _stack.emplace_back(_Enter{n_});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = List<uint64_t>::cons(_f.n_, std::move(_result));
    }
  }
  return _result;
}
