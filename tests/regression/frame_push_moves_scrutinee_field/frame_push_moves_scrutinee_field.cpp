#include "frame_push_moves_scrutinee_field.h"

/// The inner fixpoint's machine matches s, which it owns, binding its
/// head x by reference into it.  The frame saved for weigh1 ys keeps
/// x, which what follows reads; the call passes s on whole, so the
/// frame copies x.  It used to move it, leaving the s the call is
/// given without its head.
uint64_t FramePushMovesScrutineeField::weigh(List<List<uint64_t>> s,
                                             const List<uint64_t> &x0_) {
  // Explicit stack replaces the non-tail recursion of weigh: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    List<uint64_t> x0_;
    List<List<uint64_t>> s;
  };

  struct _call_weigh1 {
    List<uint64_t> t;
    List<List<uint64_t>> s;
  };

  struct _after_weigh1_in_Cons {
    List<uint64_t> t;
    List<uint64_t> a0;
    std::shared_ptr<List<List<uint64_t>>> a1;
  };

  struct _after_weigh_in_Cons {
    List<uint64_t> a0;
    uint64_t _tmp2;
  };

  using _frame = std::variant<_call, _call_weigh1, _after_weigh1_in_Cons,
                              _after_weigh_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{x0_, std::move(s)});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      List<uint64_t> x0_ = std::move(_f.x0_);
      List<List<uint64_t>> s = std::move(_f.s);
      _stack.emplace_back(_call_weigh1{std::move(x0_), std::move(s)});
    } else if (std::holds_alternative<_call_weigh1>(_popped)) {
      auto _f = std::move(std::get<_call_weigh1>(_popped));
      _stack.pop_back();
      const List<uint64_t> &t = _f.t;
      List<List<uint64_t>> s = std::move(_f.s);
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(s.v_mut())) {
        _result = UINT64_C(0);
      } else {
        auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(s.v_mut());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(t.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a10] = std::get<typename List<uint64_t>::Cons>(t.v());
          _stack.emplace_back(_after_weigh1_in_Cons{t, a0, a1});
          _stack.emplace_back(_call_weigh1{*a10, std::move(s)});
        }
      }
    } else if (std::holds_alternative<_after_weigh1_in_Cons>(_popped)) {
      auto _f = std::move(std::get<_after_weigh1_in_Cons>(_popped));
      _stack.pop_back();
      List<uint64_t> t = std::move(_f.t);
      List<uint64_t> a0 = std::move(_f.a0);
      std::shared_ptr<List<List<uint64_t>>> a1 = std::move(_f.a1);
      _stack.emplace_back(_after_weigh_in_Cons{std::move(a0), _result});
      _stack.emplace_back(_call{std::move(t), *a1});
    } else {
      auto _f = std::move(std::get<_after_weigh_in_Cons>(_popped));
      _stack.pop_back();
      List<uint64_t> a0 = std::move(_f.a0);
      _result = ((_f._tmp2 + a0.length()) + _result);
    }
  }
  return _result;
}
