#include "loopify_name_hygiene.h"

/// Loopification invents C++ names -- the frame structs _Enter and
/// _Resume_<Ctor>, and the locals _stack, _result, _self -- without
/// checking whether the Rocq source already spells them.  A program that does
/// is miscompiled: the generated names capture the user's, and the loop body
/// reads the frame stack where it meant to read a constant.
uint64_t
LoopifyNameHygiene::depth(const LoopifyNameHygiene::Frame_
                              &f) { /// CraneEnter: captures varying parameters
                                    /// for each recursive call.

  struct CraneEnter {
    const LoopifyNameHygiene::Frame_ *f;
  };

  /// CraneCont_Resume_Cons_: resumes after recursive call, then processes rest.
  struct CraneCont_Resume_Cons_ {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_Resume_Cons_>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&f});
  /// Loopified depth: CraneEnter -> CraneCont_Resume_Cons_.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const LoopifyNameHygiene::Frame_ &f = *_f.f;
      if (std::holds_alternative<typename LoopifyNameHygiene::Frame_::Enter_>(
              f.v())) {
        const auto &[a0] =
            std::get<typename LoopifyNameHygiene::Frame_::Enter_>(f.v());
        _result = std::move(a0);
      } else {
        const auto &[a0] =
            std::get<typename LoopifyNameHygiene::Frame_::Resume_Cons_>(f.v());
        _stack.emplace_back(CraneCont_Resume_Cons_{});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Resume_Cons_>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

LoopifyNameHygiene::Frame_ LoopifyNameHygiene::mk(uint64_t n) {
  std::optional<LoopifyNameHygiene::Frame_> _root{};
  std::shared_ptr<LoopifyNameHygiene::Frame_> *_write = nullptr;
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      auto _value = Frame_::enter_(UINT64_C(1));
      (_write ? *(*_write = std::make_shared<LoopifyNameHygiene::Frame_>(
                      std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      uint64_t k = _loop_n - 1;
      auto _cell = typename LoopifyNameHygiene::Frame_::Resume_Cons_(nullptr);
      LoopifyNameHygiene::Frame_ &_node =
          (_write ? *(*_write = std::make_shared<LoopifyNameHygiene::Frame_>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write = &std::get<typename LoopifyNameHygiene::Frame_::Resume_Cons_>(
                    _node.v_mut())
                    .a0;
      _loop_n = k;
      continue;
    }
  }
  return std::move(*_root);
}

uint64_t
LoopifyNameHygiene::locals(uint64_t n) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_k: resumes after recursive call, then processes rest.
  struct CraneCont_k {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_k>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified locals: CraneEnter -> CraneCont_k.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = ((stack_ + result_) + self_);
      } else {
        uint64_t k = n - 1;
        _stack.emplace_back(CraneCont_k{});
        _stack.emplace_back(CraneEnter{k});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_k>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}
