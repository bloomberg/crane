#include "loopify_name_hygiene.h"

/// Loopification invents C++ names -- the frame structs _Enter and
/// _Resume_<Ctor>, and the locals _stack, _result, _self -- without
/// checking whether the Rocq source already spells them.  A program that does
/// is miscompiled: the generated names capture the user's, and the loop body
/// reads the frame stack where it meant to read a constant.
uint64_t LoopifyNameHygiene::depth(
    const LoopifyNameHygiene::Frame_
        &f) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyNameHygiene::Frame_ *f;
  };

  /// _Resume_Resume_Cons_: resumes after recursive call with _result.
  struct _Resume_Resume_Cons_ {};

  using _Frame = std::variant<_Enter, _Resume_Resume_Cons_>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&f});
  /// Loopified depth: _Enter -> _Resume_Resume_Cons_.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyNameHygiene::Frame_ &f = *_f.f;
      if (std::holds_alternative<typename LoopifyNameHygiene::Frame_::Enter_>(
              f.v())) {
        const auto &[a0] =
            std::get<typename LoopifyNameHygiene::Frame_::Enter_>(f.v());
        _result = std::move(a0);
      } else {
        const auto &[a0] =
            std::get<typename LoopifyNameHygiene::Frame_::Resume_Cons_>(f.v());
        _stack.emplace_back(_Resume_Resume_Cons_{});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Resume_Cons_>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

LoopifyNameHygiene::Frame_
LoopifyNameHygiene::mk(uint64_t n) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_k: resumes after recursive call with _result.
  struct _Resume_k {};

  using _Frame = std::variant<_Enter, _Resume_k>;
  LoopifyNameHygiene::Frame_ _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified mk: _Enter -> _Resume_k.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = Frame_::enter_(UINT64_C(1));
      } else {
        uint64_t k = n - 1;
        _stack.emplace_back(_Resume_k{});
        _stack.emplace_back(_Enter{k});
      }
    } else {
      auto _f = std::move(std::get<_Resume_k>(_frame));
      _result = Frame_::resume_cons_(std::move(_result));
    }
  }
  return _result;
}

uint64_t
LoopifyNameHygiene::locals(uint64_t n) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_k: resumes after recursive call with _result.
  struct _Resume_k {};

  using _Frame = std::variant<_Enter, _Resume_k>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  /// Loopified locals: _Enter -> _Resume_k.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = ((stack_ + result_) + self_);
      } else {
        uint64_t k = n - 1;
        _stack.emplace_back(_Resume_k{});
        _stack.emplace_back(_Enter{k});
      }
    } else {
      auto _f = std::move(std::get<_Resume_k>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}
