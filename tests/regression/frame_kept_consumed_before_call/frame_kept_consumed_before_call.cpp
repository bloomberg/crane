#include "frame_kept_consumed_before_call.h"

List<uint64_t> FrameKeptConsumedBeforeCall::snoc(List<uint64_t> x) {
  crane::rc<List<uint64_t>> _head{};
  crane::rc<List<uint64_t>> *_write = &_head;
  crane::rc<List<uint64_t>> _own = crane::rc<List<uint64_t>>();
  bool _uniq = true;
  const List<uint64_t> *_loop_x = &x;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_x->v())) {
      *_write = crane::make_rc<List<uint64_t>>(
          List<uint64_t>::cons(UINT64_C(0), List<uint64_t>::nil()));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_loop_x->v());
      auto _rs = crane::reuse_step(_own, _uniq, a1);
      auto _cell = crane::make_rc_reusing_unchecked(
          std::move(_rs.token), typename List<uint64_t>::Cons(a0, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _own = std::move(_rs.next);
      _loop_x = _own.get();
      continue;
    }
  }
  return std::move(*_head);
}

List<List<uint64_t>> FrameKeptConsumedBeforeCall::pairs(
    uint64_t fuel,
    List<List<uint64_t>> l) { /// CraneEnter: captures varying parameters for
                              /// each recursive call.

  struct CraneEnter {
    List<List<uint64_t>> l;
    uint64_t fuel;
  };

  /// CraneCont_Cons: saves [a0, y], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons {
    List<uint64_t> a0;
    List<uint64_t> y;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<List<uint64_t>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{std::move(l), fuel});
  /// Loopified pairs: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      List<List<uint64_t>> l = std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        uint64_t k = fuel - 1;
        if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                l.v_mut())) {
          _result = List<List<uint64_t>>::nil();
        } else {
          auto &[a0, a1] =
              std::get<typename List<List<uint64_t>>::Cons>(l.v_mut());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                  _sv0.v())) {
            _result = List<List<uint64_t>>::cons(std::move(a0),
                                                 List<List<uint64_t>>::nil());
          } else {
            const auto &[a00, a10] =
                std::get<typename List<List<uint64_t>>::Cons>(_sv0.v());
            List<uint64_t> y = snoc(a0);
            _stack.emplace_back(CraneCont_Cons{std::move(a0), std::move(y)});
            _stack.emplace_back(CraneEnter{
                List<List<uint64_t>>::cons(a00, crane::child(a10)), k});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      List<uint64_t> a0 = std::move(_f.a0);
      List<uint64_t> y = std::move(_f.y);
      List<List<uint64_t>> r = std::move(_result);
      _result = List<List<uint64_t>>::cons(
          std::move(a0),
          List<List<uint64_t>>::cons(std::move(y), std::move(r)));
    }
  }
  return _result;
}

List<List<uint64_t>> FrameKeptConsumedBeforeCall::again(
    uint64_t fuel,
    List<List<uint64_t>> l) { /// CraneEnter: captures varying parameters for
                              /// each recursive call.

  struct CraneEnter {
    List<List<uint64_t>> l;
    uint64_t fuel;
  };

  /// CraneCont_Cons: saves [a0, y], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons {
    List<uint64_t> a0;
    List<uint64_t> y;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<List<uint64_t>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{std::move(l), fuel});
  /// Loopified again: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      List<List<uint64_t>> l = std::move(_f.l);
      uint64_t fuel = _f.fuel;
      if (fuel <= 0) {
        _result = std::move(l);
      } else {
        uint64_t k = fuel - 1;
        if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                l.v_mut())) {
          _result = List<List<uint64_t>>::nil();
        } else {
          auto &[a0, a1] =
              std::get<typename List<List<uint64_t>>::Cons>(l.v_mut());
          auto &&_sv0 = *a1;
          if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                  _sv0.v())) {
            _result = List<List<uint64_t>>::cons(std::move(a0),
                                                 List<List<uint64_t>>::nil());
          } else {
            const auto &[a00, a10] =
                std::get<typename List<List<uint64_t>>::Cons>(_sv0.v());
            List<uint64_t> y = snoc(a0);
            _stack.emplace_back(CraneCont_Cons{a0, std::move(y)});
            _stack.emplace_back(CraneEnter{
                List<List<uint64_t>>::cons(std::move(a0), crane::child(a10)),
                k});
          }
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      List<uint64_t> a0 = std::move(_f.a0);
      List<uint64_t> y = std::move(_f.y);
      List<List<uint64_t>> r = std::move(_result);
      _result = List<List<uint64_t>>::cons(
          std::move(y),
          List<List<uint64_t>>::cons(std::move(a0), std::move(r)));
    }
  }
  return _result;
}
