#include "loopify_name_hygiene.h"

/// Loopification invents C++ names -- the frame structs _Enter and
/// _Resume_<Ctor>, and the locals _stack, _result, _self -- without
/// checking whether the Rocq source already spells them.  A program that does
/// is miscompiled: the generated names capture the user's, and the loop body
/// reads the frame stack where it meant to read a constant.
uint64_t LoopifyNameHygiene::depth(const LoopifyNameHygiene::Frame_ &f) {
  // Explicit stack replaces the non-tail recursion of depth: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const LoopifyNameHygiene::Frame_ *f;
  };

  struct _after_depth_in_Resume_Cons_ {};

  using _frame = std::variant<_call, _after_depth_in_Resume_Cons_>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&f});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const LoopifyNameHygiene::Frame_ &f = *_f.f;
      if (std::holds_alternative<typename LoopifyNameHygiene::Frame_::Enter_>(
              f.v())) {
        const auto &[a0] =
            std::get<typename LoopifyNameHygiene::Frame_::Enter_>(f.v());
        _result = std::move(a0);
      } else {
        const auto &[a0] =
            std::get<typename LoopifyNameHygiene::Frame_::Resume_Cons_>(f.v());
        _stack.emplace_back(_after_depth_in_Resume_Cons_{});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else {
      auto _f = std::move(std::get<_after_depth_in_Resume_Cons_>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    }
  }
  return _result;
}

LoopifyNameHygiene::Frame_ LoopifyNameHygiene::mk(uint64_t n) {
  // Builds the result front to back: _write points at the empty tail the next
  // cell fills.
  std::optional<LoopifyNameHygiene::Frame_> _root{};
  std::shared_ptr<LoopifyNameHygiene::Frame_> *_write = nullptr;
  while (true) {
    if (n <= 0) {
      auto _value = Frame_::enter_(UINT64_C(1));
      (_write ? *(*_write = std::make_shared<LoopifyNameHygiene::Frame_>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t k = n - 1;
      auto _cell = typename LoopifyNameHygiene::Frame_::Resume_Cons_(nullptr);
      LoopifyNameHygiene::Frame_ &_node =
          (_write ? *(*_write = std::make_shared<LoopifyNameHygiene::Frame_>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename LoopifyNameHygiene::Frame_::Resume_Cons_>(
              _node.v_mut())
              .a0;
      n = k;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t LoopifyNameHygiene::locals(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of locals: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_locals_in_S {};

  using _frame = std::variant<_call, _after_locals_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = stack_ + result_ + self_;
      } else {
        uint64_t k = n - 1;
        _stack.emplace_back(_after_locals_in_S{});
        _stack.emplace_back(_call{k});
      }
    } else {
      auto _f = std::move(std::get<_after_locals_in_S>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    }
  }
  return _result;
}
