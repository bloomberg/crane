#include <loopify_list_generation.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
LoopifyListGeneration::replicate(const unsigned int n, const unsigned int x) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = List<unsigned int>::ctor::Nil_();
                            } else {
                              unsigned int n_ = n - 1;
                              _stack.push_back(_Call1{x});
                              _stack.push_back(_Enter{std::move(n_)});
                            }
                          },
                          [&](_Call1 _f) {
                            _result = List<unsigned int>::ctor::Cons_(_f._s0,
                                                                      _result);
                          }},
               _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListGeneration::stutter(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
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
                  Overloaded{[&](const typename List<unsigned int>::Nil _args)
                                 -> void {
                               _result = List<unsigned int>::ctor::Nil_();
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               _stack.push_back(_Call1{_args.d_a0, _args.d_a0});
                               _stack.push_back(_Enter{_args.d_a1});
                             }},
                  l->v());
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::ctor::Cons_(
                  _f._s0, List<unsigned int>::ctor::Cons_(_f._s1, _result));
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListGeneration::cycle(const unsigned int n,
                             const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = List<unsigned int>::ctor::Nil_();
                            } else {
                              unsigned int n_ = n - 1;
                              _stack.push_back(_Call1{l});
                              _stack.push_back(_Enter{n_});
                            }
                          },
                          [&](_Call1 _f) { _result = _f._s0->app(_result); }},
               _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListGeneration::iterate(const unsigned int n, const unsigned int x) {
  struct _Enter {
    const unsigned int x;
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{x, n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int x = _f.x;
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = List<unsigned int>::ctor::Nil_();
                            } else {
                              unsigned int n_ = n - 1;
                              _stack.push_back(_Call1{x});
                              _stack.push_back(_Enter{(x + 1u), std::move(n_)});
                            }
                          },
                          [&](_Call1 _f) {
                            _result = List<unsigned int>::ctor::Cons_(_f._s0,
                                                                      _result);
                          }},
               _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListGeneration::replicate_list(
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l) {
  struct _Enter {
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> l;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
                  l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::pair<unsigned int, unsigned int>>::Nil _args)
                          -> void {
                        _result = List<unsigned int>::ctor::Nil_();
                      },
                      [&](const typename List<
                          std::pair<unsigned int, unsigned int>>::Cons _args)
                          -> void {
                        unsigned int n = _args.d_a0.first;
                        unsigned int x = _args.d_a0.second;
                        std::shared_ptr<List<unsigned int>> rep =
                            replicate(n, x);
                        _stack.push_back(_Call1{std::move(rep)});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = _f._s0->app(_result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListGeneration::repeat_with_sep(
    const unsigned int sep, const unsigned int n, const unsigned int x) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
    const unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = List<unsigned int>::ctor::Nil_();
                            } else {
                              unsigned int n_ = n - 1;
                              if (n_ <= 0) {
                                _result = List<unsigned int>::ctor::Cons_(
                                    x, List<unsigned int>::ctor::Nil_());
                              } else {
                                unsigned int _x = n_ - 1;
                                _stack.push_back(_Call1{x, sep});
                                _stack.push_back(_Enter{n_});
                              }
                            }
                          },
                          [&](_Call1 _f) {
                            _result = List<unsigned int>::ctor::Cons_(
                                _f._s0, List<unsigned int>::ctor::Cons_(
                                            _f._s1, _result));
                          }},
               _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListGeneration::range(const unsigned int start, const unsigned int len) {
  struct _Enter {
    const unsigned int len;
    const unsigned int start;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{len, start});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int len = _f.len;
                            const unsigned int start = _f.start;
                            if (len <= 0) {
                              _result = List<unsigned int>::ctor::Nil_();
                            } else {
                              unsigned int len_ = len - 1;
                              _stack.push_back(_Call1{start});
                              _stack.push_back(_Enter{len_, (start + 1u)});
                            }
                          },
                          [&](_Call1 _f) {
                            _result = List<unsigned int>::ctor::Cons_(_f._s0,
                                                                      _result);
                          }},
               _frame);
  }
  return _result;
}
