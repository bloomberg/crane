#include <loopify_list_combining.h>

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

std::shared_ptr<List<unsigned int>>
LoopifyListCombining::append(const std::shared_ptr<List<unsigned int>> &a,
                             std::shared_ptr<List<unsigned int>> b) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_b = b;
  std::shared_ptr<List<unsigned int>> _loop_a = a;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = std::move(_loop_b);
              } else {
                _head = std::move(_loop_b);
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              std::shared_ptr<List<unsigned int>> _next_b = std::move(_loop_b);
              std::shared_ptr<List<unsigned int>> _next_a = _args.d_a1;
              _loop_b = std::move(_next_b);
              _loop_a = std::move(_next_a);
            }},
        _loop_a->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyListCombining::intersperse(
    const unsigned int sep, const std::shared_ptr<List<unsigned int>> &l) {
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
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
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
                              .d_a1 = List<unsigned int>::cons(
                              _args.d_a0, List<unsigned int>::nil());
                        } else {
                          _head = List<unsigned int>::cons(
                              _args.d_a0, List<unsigned int>::nil());
                        }
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
                        auto _cell =
                            List<unsigned int>::cons(_args.d_a0, nullptr);
                        auto _cell1 = List<unsigned int>::cons(sep, nullptr);
                        std::get<typename List<unsigned int>::Cons>(
                            _cell->v_mut())
                            .d_a1 = _cell1;
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell1;
                        _loop_l = _args.d_a1;
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyListCombining::intercalate(
    const std::shared_ptr<List<unsigned int>> &sep,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<
                 std::shared_ptr<List<unsigned int>>>::Cons &>()
                 .d_a0) _s0;
    const std::shared_ptr<List<unsigned int>> _s1;
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
                          -> void { _result = List<unsigned int>::nil(); },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<
                                    std::shared_ptr<List<unsigned int>>>::Nil
                                        _args0) -> void {
                                  _result = _args.d_a0;
                                },
                                [&](const typename List<
                                    std::shared_ptr<List<unsigned int>>>::Cons
                                        _args0) -> void {
                                  _stack.push_back(_Call1{_args.d_a0, sep});
                                  _stack.push_back(_Enter{_args.d_a1});
                                }},
                            _args.d_a1->v());
                      }},
                  ll->v());
            },
            [&](_Call1 _f) {
              _result = append(_f._s0, append(_f._s1, _result));
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListCombining::concat(
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
                          -> void { _result = List<unsigned int>::nil(); },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  ll->v());
            },
            [&](_Call1 _f) { _result = append(_f._s0, _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListCombining::mapcat(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(List<unsigned int>::cons(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
        List<unsigned int>::cons(
            std::declval<const typename List<unsigned int>::Cons &>().d_a0,
            List<unsigned int>::nil()))) _s0;
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
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> void { _result = List<unsigned int>::nil(); },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{List<unsigned int>::cons(
                            _args.d_a0,
                            List<unsigned int>::cons(
                                _args.d_a0, List<unsigned int>::nil()))});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = append(_f._s0, _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListCombining::interleave_two(std::shared_ptr<List<unsigned int>> l1,
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
              _result = List<unsigned int>::cons(
                  _f._s0, List<unsigned int>::cons(_f._s1, _result));
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListCombining::concat_sep(
    const unsigned int sep,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<
                 std::shared_ptr<List<unsigned int>>>::Cons &>()
                 .d_a0) _s0;
    const unsigned int _s1;
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
                          -> void { _result = List<unsigned int>::nil(); },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<
                                    std::shared_ptr<List<unsigned int>>>::Nil
                                        _args0) -> void {
                                  _result = _args.d_a0;
                                },
                                [&](const typename List<
                                    std::shared_ptr<List<unsigned int>>>::Cons
                                        _args0) -> void {
                                  _stack.push_back(_Call1{_args.d_a0, sep});
                                  _stack.push_back(_Enter{_args.d_a1});
                                }},
                            _args.d_a1->v());
                      }},
                  ll->v());
            },
            [&](_Call1 _f) {
              _result =
                  append(_f._s0, List<unsigned int>::cons(_f._s1, _result));
            }},
        _frame);
  }
  return _result;
}
