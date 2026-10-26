#include "frame_push_moves_scrutinee_field.h"

/// The inner fixpoint's machine matches s, which it owns, binding its
/// head x by reference into it.  The frame saved for weigh1 ys keeps
/// x, which what follows reads; the call passes s on whole, so the
/// frame copies x.  It used to move it, leaving the s the call is
/// given without its head.
uint64_t FramePushMovesScrutineeField::weigh(
    List<List<uint64_t>> s,
    const List<uint64_t> &x0_) { /// CraneEnter: captures varying parameters for
                                 /// each recursive call.

  struct CraneEnter {
    List<uint64_t> x0_;
    List<List<uint64_t>> s;
  };

  /// CraneEnter_weigh1: captures varying parameters for each recursive call.
  struct CraneEnter_weigh1 {
    List<uint64_t> t;
    List<List<uint64_t>> s;
  };

  /// CraneCont_Cons: saves [t, a0, a1], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons {
    List<uint64_t> t;
    List<uint64_t> a0;
    std::shared_ptr<List<List<uint64_t>>> a1;
  };

  /// CraneCont_Cons_1: saves [a0, _tmp2], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons_1 {
    List<uint64_t> a0;
    uint64_t _tmp2;
  };

  using CraneFrame = std::variant<CraneEnter, CraneEnter_weigh1, CraneCont_Cons,
                                  CraneCont_Cons_1>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{x0_, std::move(s)});
  /// Loopified weigh: CraneEnter -> CraneCont_Cons -> CraneCont_Cons_1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &x0_ = std::move(_f.x0_);
      List<List<uint64_t>> s = std::move(_f.s);
      _stack.emplace_back(CraneEnter_weigh1{x0_, std::move(s)});
    } else if (std::holds_alternative<CraneEnter_weigh1>(_frame)) {
      auto _f = std::move(std::get<CraneEnter_weigh1>(_frame));
      const List<uint64_t> &t = std::move(_f.t);
      List<List<uint64_t>> s = std::move(_f.s);
      if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
              s.v_mut())) {
        _result = UINT64_C(0);
      } else {
        auto &[a0, a1] =
            std::get<typename List<List<uint64_t>>::Cons>(s.v_mut());
        if (std::holds_alternative<typename List<uint64_t>::Nil>(t.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a00, a10] =
              std::get<typename List<uint64_t>::Cons>(t.v());
          _stack.emplace_back(CraneCont_Cons{t, a0, a1});
          _stack.emplace_back(CraneEnter_weigh1{*a10, s});
        }
      }
    } else if (std::holds_alternative<CraneCont_Cons>(_frame)) {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      const List<uint64_t> &t = std::move(_f.t);
      List<uint64_t> a0 = std::move(_f.a0);
      std::shared_ptr<List<List<uint64_t>>> a1 = std::move(_f.a1);
      _stack.emplace_back(CraneCont_Cons_1{std::move(a0), std::move(_result)});
      _stack.emplace_back(CraneEnter{t, *a1});
    } else {
      auto _f = std::move(std::get<CraneCont_Cons_1>(_frame));
      List<uint64_t> a0 = std::move(_f.a0);
      _result = ((_f._tmp2 + a0.length()) + std::move(_result));
    }
  }
  return _result;
}
