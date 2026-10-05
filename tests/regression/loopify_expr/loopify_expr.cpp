#include "loopify_expr.h"

/// sum_shapes l sums values from shapes using unified pattern.
/// Tests or-pattern style matching in Coq.
uint64_t LoopifyExpr::sum_shapes(const List<LoopifyExpr::shape> &l) {
  {
    const List<LoopifyExpr::shape> &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = std::move(_lc1_acc);
    const List<LoopifyExpr::shape> *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<typename List<LoopifyExpr::shape>::Nil>(
              _lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyExpr::shape>::Cons>(
                _lc1_loop_l0->v());
        uint64_t val = [&]() {
          if (std::holds_alternative<typename LoopifyExpr::shape::Circle>(
                  a0.v())) {
            const auto &[a00] =
                std::get<typename LoopifyExpr::shape::Circle>(a0.v());
            return a00;
          } else if (std::holds_alternative<
                         typename LoopifyExpr::shape::Square>(a0.v())) {
            const auto &[a00] =
                std::get<typename LoopifyExpr::shape::Square>(a0.v());
            return a00;
          } else {
            const auto &[a00] =
                std::get<typename LoopifyExpr::shape::Triangle>(a0.v());
            return a00;
          }
        }();
        _lc1_loop_acc = (_lc1_loop_acc + val);
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}

/// count_by_shape l counts shapes: (circles, squares, triangles).
std::pair<std::pair<uint64_t, uint64_t>, uint64_t> LoopifyExpr::count_by_shape(
    const List<LoopifyExpr::shape> &l) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    const List<LoopifyExpr::shape> *l;
  };

  /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Cons {
    LoopifyExpr::shape a0;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
  std::pair<std::pair<uint64_t, uint64_t>, uint64_t> _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&l});
  /// Loopified count_by_shape: CraneEnter -> CraneCont_Cons.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const List<LoopifyExpr::shape> &l = *_f.l;
      if (std::holds_alternative<typename List<LoopifyExpr::shape>::Nil>(
              l.v())) {
        _result = std::make_pair(std::make_pair(UINT64_C(0), UINT64_C(0)),
                                 UINT64_C(0));
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyExpr::shape>::Cons>(l.v());
        _stack.emplace_back(CraneCont_Cons{a0});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Cons>(_frame));
      LoopifyExpr::shape a0 = std::move(_f.a0);
      auto [p, t] = std::move(_result);
      auto [c, sq] = std::move(p);
      if (std::holds_alternative<typename LoopifyExpr::shape::Circle>(a0.v())) {
        _result = std::make_pair(std::make_pair((c + 1), sq), t);
      } else if (std::holds_alternative<typename LoopifyExpr::shape::Square>(
                     a0.v())) {
        _result = std::make_pair(std::make_pair(c, (sq + 1)), t);
      } else {
        _result = std::make_pair(std::make_pair(c, sq), (t + 1));
      }
    }
  }
  return _result;
}
