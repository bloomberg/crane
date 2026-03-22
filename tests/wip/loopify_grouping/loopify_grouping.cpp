#include <loopify_grouping.h>

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

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyGrouping::prepend_to_groups(
    const unsigned int x, const bool same,
    std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> groups) {
  if (same) {
    return [&](void) {
      if (std::move(groups).use_count() == 1 &&
          std::move(groups)->v().index() == 1) {
        auto &_rf = std::get<1>(std::move(groups)->v_mut());
        std::shared_ptr<List<unsigned int>> g = std::move(_rf.d_a0);
        std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> gs =
            std::move(_rf.d_a1);
        _rf.d_a0 = List<unsigned int>::ctor::Cons_(x, g);
        _rf.d_a1 = std::move(gs);
        return std::move(groups);
      } else {
        return std::visit(
            Overloaded{
                [&](const typename List<
                    std::shared_ptr<List<unsigned int>>>::Nil _args)
                    -> std::shared_ptr<
                        List<std::shared_ptr<List<unsigned int>>>> {
                  return List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                      List<unsigned int>::ctor::Cons_(
                          std::move(x), List<unsigned int>::ctor::Nil_()),
                      List<std::shared_ptr<List<unsigned int>>>::ctor::Nil_());
                },
                [&](const typename List<
                    std::shared_ptr<List<unsigned int>>>::Cons _args)
                    -> std::shared_ptr<
                        List<std::shared_ptr<List<unsigned int>>>> {
                  return List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                      List<unsigned int>::ctor::Cons_(std::move(x), _args.d_a0),
                      _args.d_a1);
                }},
            std::move(groups)->v());
      }
    }();
  } else {
    return List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
        List<unsigned int>::ctor::Cons_(std::move(x),
                                        List<unsigned int>::ctor::Nil_()),
        std::move(groups));
  }
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyGrouping::group_fuel(const unsigned int fuel,
                            const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
    const typename List<unsigned int>::Cons _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result =
                    List<std::shared_ptr<List<unsigned int>>>::ctor::Nil_();
              } else {
                unsigned int fuel_ = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> void {
                          _result = List<std::shared_ptr<List<unsigned int>>>::
                              ctor::Nil_();
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil
                                          _args0) -> void {
                                    _result = List<
                                        std::shared_ptr<List<unsigned int>>>::
                                        ctor::Cons_(
                                            List<unsigned int>::ctor::Cons_(
                                                _args.d_a0, List<unsigned int>::
                                                                ctor::Nil_()),
                                            List<std::shared_ptr<List<
                                                unsigned int>>>::ctor::Nil_());
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          _args0) -> void {
                                    _stack.push_back(_Call1{_args, _args0});
                                    _stack.push_back(
                                        _Enter{List<unsigned int>::ctor::Cons_(
                                                   _args0.d_a0, _args0.d_a1),
                                               fuel_});
                                  }},
                              _args.d_a1->v());
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              const typename List<unsigned int>::Cons _args0 = _f._s1;
              std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                  rec_result = _result;
              _result = prepend_to_groups(_args.d_a0, _args.d_a0 == _args0.d_a0,
                                          std::move(rec_result));
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyGrouping::group(const std::shared_ptr<List<unsigned int>> &l) {
  return group_fuel(l->length(), l);
}

__attribute__((pure)) bool
LoopifyGrouping::elem(const unsigned int x,
                      const std::shared_ptr<List<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                            _result = false;
                            _continue = false;
                          },
                          [&](const typename List<unsigned int>::Cons _args) {
                            if (x == _args.d_a0) {
                              _result = true;
                              _continue = false;
                            } else {
                              _loop_l = _args.d_a1;
                            }
                          }},
               _loop_l->v());
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyGrouping::nub(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
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
                               _stack.push_back(_Call1{_args});
                               _stack.push_back(_Enter{_args.d_a1});
                             }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::shared_ptr<List<unsigned int>> rest = _result;
              if (elem(_args.d_a0, rest)) {
                _result = std::move(rest);
              } else {
                _result = List<unsigned int>::ctor::Cons_(_args.d_a0,
                                                          std::move(rest));
              }
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyGrouping::remove_elem(const unsigned int x,
                             const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int x;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, x});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              const unsigned int x = _f.x;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> void {
                        _result = List<unsigned int>::ctor::Nil_();
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        if (x == _args.d_a0) {
                          _stack.push_back(_Enter{_args.d_a1, std::move(x)});
                        } else {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1, std::move(x)});
                        }
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) std::pair<std::pair<std::shared_ptr<List<unsigned int>>,
                                          std::shared_ptr<List<unsigned int>>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifyGrouping::partition3(const unsigned int pivot,
                            const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const unsigned int _s0;
    const typename List<unsigned int>::Cons _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::pair<std::shared_ptr<List<unsigned int>>,
                      std::shared_ptr<List<unsigned int>>>,
            std::shared_ptr<List<unsigned int>>>
      _result{};
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
                               _result = std::make_pair(
                                   std::make_pair(
                                       List<unsigned int>::ctor::Nil_(),
                                       List<unsigned int>::ctor::Nil_()),
                                   List<unsigned int>::ctor::Nil_());
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               _stack.push_back(_Call1{pivot, _args});
                               _stack.push_back(_Enter{_args.d_a1});
                             }},
                  l->v());
            },
            [&](_Call1 _f) {
              const unsigned int pivot = _f._s0;
              const typename List<unsigned int>::Cons _args = _f._s1;
              std::pair<std::shared_ptr<List<unsigned int>>,
                        std::shared_ptr<List<unsigned int>>>
                  p = _result.first;
              std::shared_ptr<List<unsigned int>> greater = _result.second;
              std::shared_ptr<List<unsigned int>> less = p.first;
              std::shared_ptr<List<unsigned int>> equal = p.second;
              if (_args.d_a0 < pivot) {
                _result = std::make_pair(
                    std::make_pair(
                        List<unsigned int>::ctor::Cons_(_args.d_a0, less),
                        equal),
                    greater);
              } else {
                if (pivot < _args.d_a0) {
                  _result = std::make_pair(
                      std::make_pair(less, equal),
                      List<unsigned int>::ctor::Cons_(_args.d_a0, greater));
                } else {
                  _result = std::make_pair(
                      std::make_pair(less, List<unsigned int>::ctor::Cons_(
                                               _args.d_a0, equal)),
                      greater);
                }
              }
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyGrouping::count_elem(const unsigned int x,
                            const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(1u) _s0;
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
                                 -> void { _result = 0u; },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               if (x == _args.d_a0) {
                                 _stack.push_back(_Call1{1u});
                                 _stack.push_back(_Enter{_args.d_a1});
                               } else {
                                 _stack.push_back(_Enter{_args.d_a1});
                               }
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyGrouping::group_pairs(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::make_pair(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
        std::declval<const typename List<unsigned int>::Cons &>().d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _result{};
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
                          -> void {
                        _result = List<std::pair<unsigned int,
                                                 unsigned int>>::ctor::Nil_();
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0) -> void {
                                  _result = List<
                                      std::pair<unsigned int,
                                                unsigned int>>::ctor::Nil_();
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0) -> void {
                                  std::visit(
                                      Overloaded{
                                          [&](const typename List<
                                              unsigned int>::Nil _args1)
                                              -> void {
                                            _result =
                                                List<std::pair<unsigned int,
                                                               unsigned int>>::
                                                    ctor::Nil_();
                                          },
                                          [&](const typename List<
                                              unsigned int>::Cons _args1)
                                              -> void {
                                            _stack.push_back(
                                                _Call1{std::make_pair(
                                                    _args.d_a0, _args1.d_a0)});
                                            _stack.push_back(
                                                _Enter{_args1.d_a1});
                                          }},
                                      _args.d_a1->v());
                                }},
                            _args.d_a1->v());
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              _result =
                  List<std::pair<unsigned int, unsigned int>>::ctor::Cons_(
                      _f._s0, _result);
            }},
        _frame);
  }
  return _result;
}
