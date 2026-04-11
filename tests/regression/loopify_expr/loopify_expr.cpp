#include <loopify_expr.h>

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// sum_shapes l sums values from shapes using unified pattern.
/// Tests or-pattern style matching in Coq.
__attribute__((pure)) unsigned int LoopifyExpr::sum_shapes(
    const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>> &l) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>>
                  l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::shared_ptr<LoopifyExpr::shape>>::Nil _args)
                          -> void { _result = 0u; },
                      [&](const typename List<
                          std::shared_ptr<LoopifyExpr::shape>>::Cons _args)
                          -> void {
                        unsigned int val = std::visit(
                            Overloaded{
                                [](const typename LoopifyExpr::shape::Circle
                                       _args0) -> unsigned int {
                                  return _args0.d_a0;
                                },
                                [](const typename LoopifyExpr::shape::Square
                                       _args0) -> unsigned int {
                                  return _args0.d_a0;
                                },
                                [](const typename LoopifyExpr::shape::Triangle
                                       _args0) -> unsigned int {
                                  return _args0.d_a0;
                                }},
                            _args.d_a0->v());
                        _stack.push_back(_Call1{val});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

/// count_by_shape l counts shapes: (circles, squares, triangles).
__attribute__((pure))
std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
LoopifyExpr::count_by_shape(
    const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>> &l) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>> l;
  };

  struct _Call1 {
    const typename List<std::shared_ptr<LoopifyExpr::shape>>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::pair<unsigned int, unsigned int>, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>>
                  l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::shared_ptr<LoopifyExpr::shape>>::Nil _args)
                          -> void {
                        _result = std::make_pair(std::make_pair(0u, 0u), 0u);
                      },
                      [&](const typename List<
                          std::shared_ptr<LoopifyExpr::shape>>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename List<std::shared_ptr<LoopifyExpr::shape>>::Cons
                  _args = _f._s0;
              std::pair<unsigned int, unsigned int> p = _result.first;
              unsigned int t = _result.second;
              unsigned int c = p.first;
              unsigned int sq = p.second;
              _result = std::visit(
                  Overloaded{
                      [&](const typename LoopifyExpr::shape::Circle _args0)
                          -> std::pair<std::pair<unsigned int, unsigned int>,
                                       unsigned int> {
                        return std::make_pair(std::make_pair((c + 1), sq), t);
                      },
                      [&](const typename LoopifyExpr::shape::Square _args0)
                          -> std::pair<std::pair<unsigned int, unsigned int>,
                                       unsigned int> {
                        return std::make_pair(std::make_pair(c, (sq + 1)), t);
                      },
                      [&](const typename LoopifyExpr::shape::Triangle _args0)
                          -> std::pair<std::pair<unsigned int, unsigned int>,
                                       unsigned int> {
                        return std::make_pair(std::make_pair(c, sq), (t + 1));
                      }},
                  _args.d_a0->v());
            }},
        _frame);
  }
  return _result;
}
