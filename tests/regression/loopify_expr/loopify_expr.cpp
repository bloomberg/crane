#include "loopify_expr.h"

/// sum_shapes l sums values from shapes using unified pattern.
/// Tests or-pattern style matching in Coq.
uint64_t LoopifyExpr::sum_shapes(
    const List<LoopifyExpr::shape>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyExpr::shape> *l;
  };

  /// _Resume_Cons: saves [val], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t val;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum_shapes: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyExpr::shape> &l = *_f.l;
      if (std::holds_alternative<typename List<LoopifyExpr::shape>::Nil>(
              l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyExpr::shape>::Cons>(l.v());
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
        _stack.emplace_back(_Resume_Cons{val});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.val + std::move(_result));
    }
  }
  return _result;
}

/// count_by_shape l counts shapes: (circles, squares, triangles).
std::pair<std::pair<uint64_t, uint64_t>, uint64_t> LoopifyExpr::count_by_shape(
    const List<LoopifyExpr::shape>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyExpr::shape> *l;
  };

  /// _Cont_Cons: saves [a0], resumes after recursive call, then processes rest.
  struct _Cont_Cons {
    LoopifyExpr::shape a0;
  };

  using _Frame = std::variant<_Enter, _Cont_Cons>;
  std::pair<std::pair<uint64_t, uint64_t>, uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified count_by_shape: _Enter -> _Cont_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const List<LoopifyExpr::shape> &l = *_f.l;
      if (std::holds_alternative<typename List<LoopifyExpr::shape>::Nil>(
              l.v())) {
        _result = std::make_pair(std::make_pair(UINT64_C(0), UINT64_C(0)),
                                 UINT64_C(0));
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyExpr::shape>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      LoopifyExpr::shape a0 = std::move(_f.a0);
      auto _cs = std::move(_result);
      std::pair<uint64_t, uint64_t> p = std::move(_cs.first);
      uint64_t t = std::move(_cs.second);
      uint64_t c = std::move(p.first);
      uint64_t sq = std::move(p.second);
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
