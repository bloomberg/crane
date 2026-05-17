#include "loopify_expr.h"

/// sum_shapes l sums values from shapes using unified pattern.
/// Tests or-pattern style matching in Coq.
unsigned int LoopifyExpr::sum_shapes(
    const List<LoopifyExpr::shape>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const List<LoopifyExpr::shape> *l;
  };

  /// _Resume_Cons: saves [val], resumes after recursive call with _result.
  struct _Resume_Cons {
    unsigned int val;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  unsigned int _result{};
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
        _result = 0u;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyExpr::shape>::Cons>(l.v());
        unsigned int val = [&]() {
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
      _result = (_f.val + _result);
    }
  }
  return _result;
}

/// count_by_shape l counts shapes: (circles, squares, triangles).
std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
LoopifyExpr::count_by_shape(
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
  std::pair<std::pair<unsigned int, unsigned int>, unsigned int> _result{};
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
        _result = std::make_pair(std::make_pair(0u, 0u), 0u);
      } else {
        const auto &[a0, a1] =
            std::get<typename List<LoopifyExpr::shape>::Cons>(l.v());
        _stack.emplace_back(_Cont_Cons{a0});
        _stack.emplace_back(_Enter{a1.get()});
      }
    } else {
      auto _f = std::move(std::get<_Cont_Cons>(_frame));
      LoopifyExpr::shape a0 = std::move(_f.a0);
      const std::pair<unsigned int, unsigned int> &p = _result.first;
      const unsigned int &t = _result.second;
      const unsigned int &c = p.first;
      const unsigned int &sq = p.second;
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
