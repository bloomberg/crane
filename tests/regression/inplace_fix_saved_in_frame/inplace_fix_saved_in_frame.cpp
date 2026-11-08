#include "inplace_fix_saved_in_frame.h"

List<List<uint64_t>> InplaceFixSavedInFrame::insert_shift(
    uint64_t x,
    const List<uint64_t> &l) { /// CraneEnter: captures varying parameters for
                               /// each recursive call.

  struct CraneEnter {
    const List<uint64_t> *l;
  };

  /// CraneCont_Cons: saves [l, k, map_k], resumes after recursive call, then
  /// processes rest.
  struct CraneCont_Cons {
    List<uint64_t> l;
    uint64_t k;
    crane::fn<List<List<uint64_t>>(List<List<uint64_t>>)> map_k;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  List<List<uint64_t>> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified insert_shift: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<uint64_t> &l = *_f.l;
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
        _result = List<List<uint64_t>>::cons(
            List<uint64_t>::cons(x, List<uint64_t>::nil()),
            List<List<uint64_t>>::nil());
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
        const List<uint64_t> &a1_value = *a1;
        uint64_t k = (a0 + x);
        auto map_k = [=](List<List<uint64_t>> lsts) -> List<List<uint64_t>> {
          /// CraneEnter: captures varying parameters for each recursive call.
          struct CraneEnter {
            List<List<uint64_t>> lsts;
          };
          /// CraneCont_Cons: saves [a00], resumes after recursive call, then
          /// processes rest.
          struct CraneCont_Cons {
            List<uint64_t> a00;
          };
          using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
          List<List<uint64_t>> _result{};
          crane::small_vector<CraneFrame> _stack;
          _stack.emplace_back(CraneEnter{std::move(lsts)});
          /// Loopified map_k: CraneEnter -> CraneCont_Cons.
          while (!_stack.empty()) {
            CraneFrame _frame = std::move(_stack.back());
            _stack.pop_back();
            if (std::holds_alternative<CraneEnter>(_frame)) {
              auto _f = std::move(std::get<CraneEnter>(_frame));
              List<List<uint64_t>> lsts = std::move(_f.lsts);
              if (std::holds_alternative<typename List<List<uint64_t>>::Nil>(
                      lsts.v_mut())) {
                _result = List<List<uint64_t>>::nil();
              } else {
                auto &[a00, a10] =
                    std::get<typename List<List<uint64_t>>::Cons>(lsts.v_mut());
                _stack.emplace_back(CraneCont_Cons{std::move(a00)});
                _stack.emplace_back(CraneEnter{*a10});
              }
            } else {
              auto _f = std::move(std::get<CraneCont_Cons>(_frame));
              List<uint64_t> a00 = std::move(_f.a00);
              _result = List<List<uint64_t>>::cons(
                  List<uint64_t>::cons(k, std::move(a00)), std::move(_result));
            }
          }
          return _result;
        };
        _stack.emplace_back(CraneCont_Cons{l, k, std::move(map_k)});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      List<uint64_t> l = std::move(_f.l);
      uint64_t k = _f.k;
      crane::fn<List<List<uint64_t>>(List<List<uint64_t>>)> map_k =
          std::move(_f.map_k);
      _result = List<List<uint64_t>>::cons(
          List<uint64_t>::cons(k, List<uint64_t>::cons(x, std::move(l))),
          map_k(std::move(_result)));
    }
  }
  return _result;
}

uint64_t InplaceFixSavedInFrame::sum_heads(const List<List<uint64_t>> &ls) {
  return ls.template fold_left<uint64_t>(
      [](uint64_t acc, const List<uint64_t> &l) -> uint64_t {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          return acc;
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          return (acc + a0);
        }
      },
      UINT64_C(0));
}
