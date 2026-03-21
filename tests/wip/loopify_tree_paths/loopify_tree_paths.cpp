#include <loopify_tree_paths.h>

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

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyTreePaths::map_cons(
    const unsigned int x,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(List<unsigned int>::ctor::Cons_(
        std::declval<const unsigned int &>(),
        std::declval<
            const typename List<std::shared_ptr<List<unsigned int>>>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                  ll = _f.ll;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Nil _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<List<unsigned int>>>> {
                        _result = List<
                            std::shared_ptr<List<unsigned int>>>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<List<unsigned int>>>> {
                        _stack.push_back(_Call1{
                            List<unsigned int>::ctor::Cons_(x, _args.d_a0)});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      }},
                  ll->v());
            },
            [&](_Call1 _f) {
              _result = List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                  _f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyTreePaths::paths(const std::shared_ptr<LoopifyTreePaths::tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTreePaths::tree> t;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyTreePaths::tree::Node &>()
                 .d_a0) _s0;
    decltype(std::declval<const typename LoopifyTreePaths::tree::Node &>()
                 .d_a1) _s1;
    decltype(std::declval<const typename LoopifyTreePaths::tree::Node &>()
                 .d_a1) _s2;
  };

  struct _Call2 {
    std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _s0;
    decltype(std::declval<const typename LoopifyTreePaths::tree::Node &>()
                 .d_a1) _s1;
    decltype(std::declval<const typename LoopifyTreePaths::tree::Node &>()
                 .d_a1) _s2;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTreePaths::tree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTreePaths::tree::Leaf _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<List<unsigned int>>>> {
                        _result = List<std::shared_ptr<List<unsigned int>>>::
                            ctor::Cons_(
                                List<unsigned int>::ctor::Nil_(),
                                List<std::shared_ptr<List<unsigned int>>>::
                                    ctor::Nil_());
                        return {};
                      },
                      [&](const typename LoopifyTreePaths::tree::Node _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<List<unsigned int>>>> {
                        _stack.push_back(
                            _Call1{_args.d_a0, _args.d_a1, _args.d_a1});
                        _stack.push_back(_Enter{_args.d_a2});
                        return {};
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1, _f._s2});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) {
              _result =
                  map_cons(_f._s2, _result)->app(map_cons(_f._s1, _f._s0));
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyTreePaths::count_paths_sum_aux(
    const unsigned int acc, const unsigned int target,
    const std::shared_ptr<LoopifyTreePaths::tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTreePaths::tree> t;
    const unsigned int acc;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyTreePaths::tree::Node &>()
                 .d_a0) _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t, acc});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTreePaths::tree> t = _f.t;
              const unsigned int acc = _f.acc;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTreePaths::tree::Leaf _args)
                          -> unsigned int {
                        if (acc == target) {
                          _result = 1u;
                        } else {
                          _result = 0u;
                        }
                        return {};
                      },
                      [&](const typename LoopifyTreePaths::tree::Node _args)
                          -> unsigned int {
                        unsigned int new_acc = (acc + _args.d_a1);
                        _stack.push_back(_Call1{_args.d_a0, new_acc});
                        _stack.push_back(_Enter{_args.d_a2, new_acc});
                        return {};
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result});
              _stack.push_back(_Enter{_f._s0, _f._s1});
            },
            [&](_Call2 _f) { _result = (_result + _f._s0); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyTreePaths::count_paths_sum(
    const unsigned int target,
    const std::shared_ptr<LoopifyTreePaths::tree> &t) {
  return count_paths_sum_aux(0u, target, t);
}

__attribute__((pure)) std::optional<std::shared_ptr<List<unsigned int>>>
LoopifyTreePaths::find_path_sum(
    const unsigned int acc, const unsigned int target,
    const std::shared_ptr<LoopifyTreePaths::tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTreePaths::tree> t;
    const unsigned int acc;
  };

  struct _Call1 {
    const typename LoopifyTreePaths::tree::Node _s0;
    const unsigned int _s1;
    unsigned int _s2;
  };

  struct _Call2 {
    const typename LoopifyTreePaths::tree::Node _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::optional<std::shared_ptr<List<unsigned int>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t, acc});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTreePaths::tree> t = _f.t;
              const unsigned int acc = _f.acc;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTreePaths::tree::Leaf _args)
                          -> std::optional<
                              std::shared_ptr<List<unsigned int>>> {
                        if (acc == target) {
                          _result = std::make_optional<
                              std::shared_ptr<List<unsigned int>>>(
                              List<unsigned int>::ctor::Nil_());
                        } else {
                          _result = std::nullopt;
                        }
                        return {};
                      },
                      [&](const typename LoopifyTreePaths::tree::Node _args)
                          -> std::optional<
                              std::shared_ptr<List<unsigned int>>> {
                        unsigned int new_acc = (acc + _args.d_a1);
                        _stack.push_back(_Call1{_args, target, new_acc});
                        _stack.push_back(_Enter{_args.d_a0, new_acc});
                        return {};
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyTreePaths::tree::Node _args = _f._s0;
              const unsigned int target = _f._s1;
              unsigned int new_acc = _f._s2;
              if (_result.has_value()) {
                std::shared_ptr<List<unsigned int>> path = *_result;
                _result =
                    std::make_optional<std::shared_ptr<List<unsigned int>>>(
                        List<unsigned int>::ctor::Cons_(_args.d_a1,
                                                        std::move(path)));
              } else {
                _stack.push_back(_Call2{_args});
                _stack.push_back(_Enter{_args.d_a2, new_acc});
              }
            },
            [&](_Call2 _f) {
              const typename LoopifyTreePaths::tree::Node _args = _f._s0;
              if (_result.has_value()) {
                std::shared_ptr<List<unsigned int>> path = *_result;
                _result =
                    std::make_optional<std::shared_ptr<List<unsigned int>>>(
                        List<unsigned int>::ctor::Cons_(_args.d_a1,
                                                        std::move(path)));
              } else {
                _result = std::nullopt;
              }
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyTreePaths::max_path_sum(
    const std::shared_ptr<LoopifyTreePaths::tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTreePaths::tree> t;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyTreePaths::tree::Node &>()
                 .d_a0) _s0;
    decltype(std::declval<const typename LoopifyTreePaths::tree::Node &>()
                 .d_a1) _s1;
  };

  struct _Call2 {
    unsigned int _s0;
    decltype(std::declval<const typename LoopifyTreePaths::tree::Node &>()
                 .d_a1) _s1;
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
              const std::shared_ptr<LoopifyTreePaths::tree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTreePaths::tree::Leaf _args)
                          -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyTreePaths::tree::Node _args)
                          -> unsigned int {
                        _stack.push_back(_Call1{_args.d_a0, _args.d_a1});
                        _stack.push_back(_Enter{_args.d_a2});
                        return {};
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = (_f._s1 + std::max(_result, _f._s0)); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyTreePaths::flatten_paths(
    const std::shared_ptr<LoopifyTreePaths::tree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyTreePaths::tree> t;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyTreePaths::tree::Node &>()
                 .d_a0) _s0;
    decltype(std::declval<const typename LoopifyTreePaths::tree::Node &>()
                 .d_a1) _s1;
  };

  struct _Call2 {
    std::shared_ptr<List<unsigned int>> _s0;
    decltype(std::declval<const typename LoopifyTreePaths::tree::Node &>()
                 .d_a1) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyTreePaths::tree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyTreePaths::tree::Leaf _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        _result = List<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename LoopifyTreePaths::tree::Node _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        _stack.push_back(_Call1{_args.d_a0, _args.d_a1});
                        _stack.push_back(_Enter{_args.d_a2});
                        return {};
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) {
              _result =
                  List<unsigned int>::ctor::Cons_(_f._s1, _result->app(_f._s0));
            }},
        _frame);
  }
  return _result;
}
