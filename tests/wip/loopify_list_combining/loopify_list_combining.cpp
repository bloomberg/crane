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
  struct _Enter {
    std::shared_ptr<List<unsigned int>> b;
    const std::shared_ptr<List<unsigned int>> a;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{b, a});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     std::shared_ptr<List<unsigned int>> b = _f.b;
                     const std::shared_ptr<List<unsigned int>> a = _f.a;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               _result = std::move(b);
                               return {};
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               _stack.push_back(_Call1{_args.d_a0});
                               _stack.push_back(
                                   _Enter{std::move(b), _args.d_a1});
                               return {};
                             }},
                         a->v());
                   },
                   [&](_Call1 _f) {
                     _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
                   }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListCombining::intersperse(
    const unsigned int sep, const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
    const unsigned int _s1;
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
                          -> std::shared_ptr<List<unsigned int>> {
                        _result = List<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0)
                                    -> std::shared_ptr<List<unsigned int>> {
                                  _result = List<unsigned int>::ctor::Cons_(
                                      _args.d_a0,
                                      List<unsigned int>::ctor::Nil_());
                                  return {};
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0)
                                    -> std::shared_ptr<List<unsigned int>> {
                                  _stack.push_back(_Call1{_args.d_a0, sep});
                                  _stack.push_back(_Enter{_args.d_a1});
                                  return {};
                                }},
                            _args.d_a1->v());
                        return {};
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
                          -> std::shared_ptr<List<unsigned int>> {
                        _result = List<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        std::visit(
                            Overloaded{
                                [&](const typename List<std::shared_ptr<
                                        List<unsigned int>>>::Nil _args0)
                                    -> std::shared_ptr<List<unsigned int>> {
                                  _result = _args.d_a0;
                                  return {};
                                },
                                [&](const typename List<std::shared_ptr<
                                        List<unsigned int>>>::Cons _args0)
                                    -> std::shared_ptr<List<unsigned int>> {
                                  _stack.push_back(_Call1{_args.d_a0, sep});
                                  _stack.push_back(_Enter{_args.d_a1});
                                  return {};
                                }},
                            _args.d_a1->v());
                        return {};
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
                          -> std::shared_ptr<List<unsigned int>> {
                        _result = List<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
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
    decltype(List<unsigned int>::ctor::Cons_(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
        List<unsigned int>::ctor::Cons_(
            std::declval<const typename List<unsigned int>::Cons &>().d_a0,
            List<unsigned int>::ctor::Nil_()))) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
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
                                 -> std::shared_ptr<List<unsigned int>> {
                               _result = List<unsigned int>::ctor::Nil_();
                               return {};
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               _stack.push_back(
                                   _Call1{List<unsigned int>::ctor::Cons_(
                                       _args.d_a0,
                                       List<unsigned int>::ctor::Cons_(
                                           _args.d_a0,
                                           List<unsigned int>::ctor::Nil_()))});
                               _stack.push_back(_Enter{_args.d_a1});
                               return {};
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
                          -> std::shared_ptr<List<unsigned int>> {
                        _result = std::move(l2);
                        return {};
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0)
                                    -> std::shared_ptr<List<unsigned int>> {
                                  _result = std::move(l1);
                                  return {};
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0)
                                    -> std::shared_ptr<List<unsigned int>> {
                                  _stack.push_back(
                                      _Call1{_args.d_a0, _args0.d_a0});
                                  _stack.push_back(
                                      _Enter{_args0.d_a1, _args.d_a1});
                                  return {};
                                }},
                            std::move(l2)->v());
                        return {};
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
                          -> std::shared_ptr<List<unsigned int>> {
                        _result = List<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        std::visit(
                            Overloaded{
                                [&](const typename List<std::shared_ptr<
                                        List<unsigned int>>>::Nil _args0)
                                    -> std::shared_ptr<List<unsigned int>> {
                                  _result = _args.d_a0;
                                  return {};
                                },
                                [&](const typename List<std::shared_ptr<
                                        List<unsigned int>>>::Cons _args0)
                                    -> std::shared_ptr<List<unsigned int>> {
                                  _stack.push_back(_Call1{_args.d_a0, sep});
                                  _stack.push_back(_Enter{_args.d_a1});
                                  return {};
                                }},
                            _args.d_a1->v());
                        return {};
                      }},
                  ll->v());
            },
            [&](_Call1 _f) {
              _result = append(
                  _f._s0, List<unsigned int>::ctor::Cons_(_f._s1, _result));
            }},
        _frame);
  }
  return _result;
}
