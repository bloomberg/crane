#include <loopify_tree_variants.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int LoopifyTreeVariants::ternary_sum(
    const std::shared_ptr<LoopifyTreeVariants::ternary> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTreeVariants::ternary> t;
  };

  struct _Call1 {
    const std::shared_ptr<LoopifyTreeVariants::ternary> _s0;
    const std::shared_ptr<LoopifyTreeVariants::ternary> _s1;
    decltype(std::declval<
                 const typename LoopifyTreeVariants::ternary::TNode &>()
                 .d_a1) _s2;
  };

  struct _Call2 {
    unsigned int _s0;
    const std::shared_ptr<LoopifyTreeVariants::ternary> _s1;
    decltype(std::declval<
                 const typename LoopifyTreeVariants::ternary::TNode &>()
                 .d_a1) _s2;
  };

  struct _Call3 {
    unsigned int _s0;
    unsigned int _s1;
    decltype(std::declval<
                 const typename LoopifyTreeVariants::ternary::TNode &>()
                 .d_a1) _s2;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTreeVariants::ternary> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTreeVariants::ternary::TLeaf
                              _args) -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyTreeVariants::ternary::TNode
                              _args) -> unsigned int {
                        _stack.push_back(
                            _Call1{_args.d_a2, _args.d_a0, _args.d_a1});
                        _stack.push_back(_Enter{_args.d_a3});
                        return {};
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1, _f._s2});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) {
              _stack.push_back(_Call3{_f._s0, _result, _f._s2});
              _stack.push_back(_Enter{_f._s1});
            },
            [&](_Call3 _f) {
              _result = (((_result + _f._s2) + _f._s1) + _f._s0);
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyTreeVariants::ternary_count(
    const std::shared_ptr<LoopifyTreeVariants::ternary> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTreeVariants::ternary> t;
  };

  struct _Call1 {
    const std::shared_ptr<LoopifyTreeVariants::ternary> _s0;
    const std::shared_ptr<LoopifyTreeVariants::ternary> _s1;
    decltype(1u) _s2;
  };

  struct _Call2 {
    unsigned int _s0;
    const std::shared_ptr<LoopifyTreeVariants::ternary> _s1;
    decltype(1u) _s2;
  };

  struct _Call3 {
    unsigned int _s0;
    unsigned int _s1;
    decltype(1u) _s2;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTreeVariants::ternary> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTreeVariants::ternary::TLeaf
                              _args) -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyTreeVariants::ternary::TNode
                              _args) -> unsigned int {
                        _stack.push_back(_Call1{_args.d_a2, _args.d_a0, 1u});
                        _stack.push_back(_Enter{_args.d_a3});
                        return {};
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1, _f._s2});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) {
              _stack.push_back(_Call3{_f._s0, _result, _f._s2});
              _stack.push_back(_Enter{_f._s1});
            },
            [&](_Call3 _f) {
              _result = (((_f._s2 + _result) + _f._s1) + _f._s0);
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyTreeVariants::quad_sum(
    const std::shared_ptr<LoopifyTreeVariants::quadtree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTreeVariants::quadtree> t;
  };

  struct _Call1 {
    const std::shared_ptr<LoopifyTreeVariants::quadtree> _s0;
    const std::shared_ptr<LoopifyTreeVariants::quadtree> _s1;
    const std::shared_ptr<LoopifyTreeVariants::quadtree> _s2;
  };

  struct _Call2 {
    unsigned int _s0;
    const std::shared_ptr<LoopifyTreeVariants::quadtree> _s1;
    const std::shared_ptr<LoopifyTreeVariants::quadtree> _s2;
  };

  struct _Call3 {
    unsigned int _s0;
    unsigned int _s1;
    const std::shared_ptr<LoopifyTreeVariants::quadtree> _s2;
  };

  struct _Call4 {
    unsigned int _s0;
    unsigned int _s1;
    unsigned int _s2;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTreeVariants::quadtree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTreeVariants::quadtree::QLeaf
                              _args) -> unsigned int {
                        _result = _args.d_a0;
                        return {};
                      },
                      [&](const typename LoopifyTreeVariants::quadtree::Quad
                              _args) -> unsigned int {
                        _stack.push_back(
                            _Call1{_args.d_a2, _args.d_a1, _args.d_a0});
                        _stack.push_back(_Enter{_args.d_a3});
                        return {};
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1, _f._s2});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) {
              _stack.push_back(_Call3{_f._s0, _result, _f._s2});
              _stack.push_back(_Enter{_f._s1});
            },
            [&](_Call3 _f) {
              _stack.push_back(_Call4{_f._s0, _f._s1, _result});
              _stack.push_back(_Enter{_f._s2});
            },
            [&](_Call4 _f) {
              _result = (((_result + _f._s2) + _f._s1) + _f._s0);
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyTreeVariants::leaf_tree_sum(
    const std::shared_ptr<LoopifyTreeVariants::leaf_tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTreeVariants::leaf_tree> t;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyTreeVariants::leaf_tree::LNode &>()
                 .d_a0) _s0;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTreeVariants::leaf_tree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTreeVariants::leaf_tree::LLeaf
                              _args) -> unsigned int {
                        _result = _args.d_a0;
                        return {};
                      },
                      [&](const typename LoopifyTreeVariants::leaf_tree::LNode
                              _args) -> unsigned int {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = (_result + _f._s0); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyTreeVariants::leaf_tree_max(
    const std::shared_ptr<LoopifyTreeVariants::leaf_tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTreeVariants::leaf_tree> t;
  };

  struct _Call1 {
    const typename LoopifyTreeVariants::leaf_tree::LNode _s0;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTreeVariants::leaf_tree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTreeVariants::leaf_tree::LLeaf
                              _args) -> unsigned int {
                        _result = _args.d_a0;
                        return {};
                      },
                      [&](const typename LoopifyTreeVariants::leaf_tree::LNode
                              _args) -> unsigned int {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a0});
                        return {};
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyTreeVariants::leaf_tree::LNode _args =
                  _f._s0;
              unsigned int lmax = _result;
              _stack.push_back(_Call2{lmax});
              _stack.push_back(_Enter{_args.d_a1});
            },
            [&](_Call2 _f) {
              unsigned int lmax = _f._s0;
              unsigned int rmax = _result;
              if (lmax < rmax) {
                _result = std::move(rmax);
              } else {
                _result = std::move(lmax);
              }
            }},
        _frame);
  }
  return _result;
}
