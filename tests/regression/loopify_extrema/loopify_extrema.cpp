#include <loopify_extrema.h>

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
LoopifyExtrema::maximum(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
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
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> void { _result = 0u; },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0) -> void {
                                  _result = _args.d_a0;
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0) -> void {
                                  _stack.push_back(_Call1{_args});
                                  _stack.push_back(_Enter{_args.d_a1});
                                }},
                            _args.d_a1->v());
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              unsigned int max_rest = _result;
              if (max_rest < _args.d_a0) {
                _result = _args.d_a0;
              } else {
                _result = max_rest;
              }
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyExtrema::minimum(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
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
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> void { _result = 0u; },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0) -> void {
                                  _result = _args.d_a0;
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0) -> void {
                                  _stack.push_back(_Call1{_args});
                                  _stack.push_back(_Enter{_args.d_a1});
                                }},
                            _args.d_a1->v());
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              unsigned int min_rest = _result;
              if (_args.d_a0 < min_rest) {
                _result = _args.d_a0;
              } else {
                _result = min_rest;
              }
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyExtrema::minmax(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> void { _result = std::make_pair(0u, 0u); },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0) -> void {
                                  _result =
                                      std::make_pair(_args.d_a0, _args.d_a0);
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0) -> void {
                                  _stack.push_back(_Call1{_args});
                                  _stack.push_back(_Enter{_args.d_a1});
                                }},
                            _args.d_a1->v());
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              unsigned int lo = _result.first;
              unsigned int hi = _result.second;
              _result = std::make_pair(std::min(_args.d_a0, lo),
                                       std::max(_args.d_a0, hi));
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyExtrema::lex_compare(const std::shared_ptr<List<unsigned int>> &l1,
                            const std::shared_ptr<List<unsigned int>> &l2) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              _result = std::visit(
                  Overloaded{[](const typename List<unsigned int>::Nil _args0)
                                 -> unsigned int { return 0u; },
                             [](const typename List<unsigned int>::Cons _args0)
                                 -> unsigned int { return 1u; }},
                  _loop_l2->v());
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args0) {
                        _result = 2u;
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
                        if (_args.d_a0 < _args0.d_a0) {
                          _result = 1u;
                          _continue = false;
                        } else {
                          if (_args0.d_a0 < _args.d_a0) {
                            _result = 2u;
                            _continue = false;
                          } else {
                            std::shared_ptr<List<unsigned int>> _next_l2 =
                                _args0.d_a1;
                            std::shared_ptr<List<unsigned int>> _next_l1 =
                                _args.d_a1;
                            _loop_l2 = std::move(_next_l2);
                            _loop_l1 = std::move(_next_l1);
                          }
                        }
                      }},
                  _loop_l2->v());
            }},
        _loop_l1->v());
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyExtrema::all_equal(const std::shared_ptr<List<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              _result = true;
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args0) {
                        _result = true;
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
                        if (_args.d_a0 == _args0.d_a0) {
                          _loop_l = _args.d_a1;
                        } else {
                          _result = false;
                          _continue = false;
                        }
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyExtrema::is_sorted(const std::shared_ptr<List<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              _result = true;
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args0) {
                        _result = true;
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
                        if (_args.d_a0 <= _args0.d_a0) {
                          _loop_l = _args.d_a1;
                        } else {
                          _result = false;
                          _continue = false;
                        }
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _result;
}
