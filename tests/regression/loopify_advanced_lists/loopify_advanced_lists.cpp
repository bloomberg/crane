#include <loopify_advanced_lists.h>

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

__attribute__((pure)) unsigned int
LoopifyAdvancedLists::product(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const std::shared_ptr<List<unsigned int>> l = _f.l;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> void { _result = 1u; },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               _stack.push_back(_Call1{_args.d_a0});
                               _stack.push_back(_Enter{_args.d_a1});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 * _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyAdvancedLists::compress(const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::ctor::Nil_();
              } else {
                _head = List<unsigned int>::ctor::Nil_();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args0) {
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = List<unsigned int>::ctor::Cons_(
                              _args.d_a0, List<unsigned int>::ctor::Nil_());
                        } else {
                          _head = List<unsigned int>::ctor::Cons_(
                              _args.d_a0, List<unsigned int>::ctor::Nil_());
                        }
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
                        if (_args.d_a0 == _args0.d_a0) {
                          _loop_l = _args.d_a1;
                        } else {
                          auto _cell = List<unsigned int>::ctor::Cons_(
                              _args.d_a0, nullptr);
                          if (_last) {
                            std::get<typename List<unsigned int>::Cons>(
                                _last->v_mut())
                                .d_a1 = _cell;
                          } else {
                            _head = _cell;
                          }
                          _last = _cell;
                          _loop_l = _args.d_a1;
                        }
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyAdvancedLists::pairwise_sum(
    const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::ctor::Nil_();
              } else {
                _head = List<unsigned int>::ctor::Nil_();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args0) {
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = List<unsigned int>::ctor::Nil_();
                        } else {
                          _head = List<unsigned int>::ctor::Nil_();
                        }
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
                        auto _cell = List<unsigned int>::ctor::Cons_(
                            (_args.d_a0 + _args0.d_a0), nullptr);
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell;
                        _loop_l = _args0.d_a1;
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyAdvancedLists::group_pairs(
    const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<
                    typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                    _last->v_mut())
                    .d_a1 =
                    List<std::pair<unsigned int, unsigned int>>::ctor::Nil_();
              } else {
                _head =
                    List<std::pair<unsigned int, unsigned int>>::ctor::Nil_();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args0) {
                        if (_last) {
                          std::get<typename List<
                              std::pair<unsigned int, unsigned int>>::Cons>(
                              _last->v_mut())
                              .d_a1 =
                              List<std::pair<unsigned int,
                                             unsigned int>>::ctor::Nil_();
                        } else {
                          _head = List<std::pair<unsigned int,
                                                 unsigned int>>::ctor::Nil_();
                        }
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
                        auto _cell =
                            List<std::pair<unsigned int, unsigned int>>::ctor::
                                Cons_(std::make_pair(_args.d_a0, _args0.d_a0),
                                      nullptr);
                        if (_last) {
                          std::get<typename List<
                              std::pair<unsigned int, unsigned int>>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell;
                        _loop_l = _args0.d_a1;
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyAdvancedLists::interleave(std::shared_ptr<List<unsigned int>> l1,
                                 std::shared_ptr<List<unsigned int>> l2) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l2;
    std::shared_ptr<List<unsigned int>> l1;
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
  _stack.push_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<List<unsigned int>> l2 = _f.l2;
              std::shared_ptr<List<unsigned int>> l1 = _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> void { _result = std::move(l2); },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0) -> void {
                                  _result = std::move(l1);
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0) -> void {
                                  _stack.push_back(
                                      _Call1{_args.d_a0, _args0.d_a0});
                                  _stack.push_back(
                                      _Enter{_args0.d_a1, _args.d_a1});
                                }},
                            std::move(l2)->v());
                      }},
                  l1->v());
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::ctor::Cons_(
                  _f._s0, List<unsigned int>::ctor::Cons_(_f._s1, _result));
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyAdvancedLists::concat_lists(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<
                 std::shared_ptr<List<unsigned int>>>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
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
                          -> void {
                        _result = List<unsigned int>::ctor::Nil_();
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  ll->v());
            },
            [&](_Call1 _f) { _result = _f._s0->app(_result); }},
        _frame);
  }
  return _result;
}
