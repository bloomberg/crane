#include <loopify_list_relations.h>

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

__attribute__((pure)) bool LoopifyListRelations::is_prefix_of(
    const std::shared_ptr<List<unsigned int>> &l1,
    const std::shared_ptr<List<unsigned int>> &l2) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l2;
    const std::shared_ptr<List<unsigned int>> l1;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>().d_a0 ==
             std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l2 = _f.l2;
              const std::shared_ptr<List<unsigned int>> l1 = _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> bool {
                        _result = true;
                        return {};
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> bool {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0) -> bool {
                                  _result = false;
                                  return {};
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0) -> bool {
                                  _stack.push_back(
                                      _Call1{_args.d_a0 == _args0.d_a0});
                                  _stack.push_back(
                                      _Enter{_args0.d_a1, _args.d_a1});
                                  return {};
                                }},
                            l2->v());
                        return {};
                      }},
                  l1->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 && _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) bool LoopifyListRelations::is_suffix_of(
    const std::shared_ptr<List<unsigned int>> &l1,
    const std::shared_ptr<List<unsigned int>> &l2) {
  unsigned int len1 = l1->length();
  unsigned int len2 = l2->length();
  if (len2 < len1) {
    return false;
  } else {
    unsigned int diff = (((std::move(len2) - std::move(len1)) > std::move(len2)
                              ? 0
                              : (std::move(len2) - std::move(len1))));
    std::shared_ptr<List<unsigned int>> suffix;
    std::function<std::shared_ptr<List<unsigned int>>(
        unsigned int, std::shared_ptr<List<unsigned int>>)>
        drop;
    drop = [](unsigned int n, std::shared_ptr<List<unsigned int>> xs)
        -> std::shared_ptr<List<unsigned int>> {
      std::shared_ptr<List<unsigned int>> _result;
      std::shared_ptr<List<unsigned int>> _loop_xs = xs;
      unsigned int _loop_n = n;
      bool _continue = true;
      while (_continue) {
        if (_loop_n <= 0) {
          {
            _result = _loop_xs;
            _continue = false;
          }
        } else {
          unsigned int n_ = _loop_n - 1;
          std::visit(
              Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                           _result = List<unsigned int>::ctor::Nil_();
                           _continue = false;
                         },
                         [&](const typename List<unsigned int>::Cons _args) {
                           std::shared_ptr<List<unsigned int>> _next_xs =
                               _args.d_a1;
                           unsigned int _next_n = n_;
                           _loop_xs = std::move(_next_xs);
                           _loop_n = std::move(_next_n);
                         }},
              _loop_xs->v());
        }
      }
      return _result;
    };
    suffix = drop(std::move(diff), l2);
    std::function<bool(std::shared_ptr<List<unsigned int>>,
                       std::shared_ptr<List<unsigned int>>)>
        eq;
    eq = [](std::shared_ptr<List<unsigned int>> a,
            std::shared_ptr<List<unsigned int>> b) -> bool {
      bool _result;
      std::shared_ptr<List<unsigned int>> _loop_b = b;
      std::shared_ptr<List<unsigned int>> _loop_a = a;
      bool _continue = true;
      while (_continue) {
        std::visit(
            Overloaded{
                [&](const typename List<unsigned int>::Nil _args0) {
                  _result = std::visit(
                      Overloaded{
                          [](const typename List<unsigned int>::Nil _args1)
                              -> bool { return true; },
                          [](const typename List<unsigned int>::Cons _args1)
                              -> bool { return false; }},
                      _loop_b->v());
                  _continue = false;
                },
                [&](const typename List<unsigned int>::Cons _args0) {
                  std::visit(
                      Overloaded{
                          [&](const typename List<unsigned int>::Nil _args1) {
                            _result = false;
                            _continue = false;
                          },
                          [&](const typename List<unsigned int>::Cons _args1) {
                            if (_args0.d_a0 == _args1.d_a0) {
                              std::shared_ptr<List<unsigned int>> _next_b =
                                  _args1.d_a1;
                              std::shared_ptr<List<unsigned int>> _next_a =
                                  _args0.d_a1;
                              _loop_b = std::move(_next_b);
                              _loop_a = std::move(_next_a);
                            } else {
                              _result = false;
                              _continue = false;
                            }
                          }},
                      _loop_b->v());
                }},
            _loop_a->v());
      }
      return _result;
    };
    return eq(l1, suffix);
  }
}

__attribute__((pure)) bool LoopifyListRelations::is_infix_of_aux(
    const std::shared_ptr<List<unsigned int>> &needle,
    const std::shared_ptr<List<unsigned int>> &haystack) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_haystack = haystack;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                     _result = std::visit(
                         Overloaded{
                             [](const typename List<unsigned int>::Nil _args0)
                                 -> bool { return true; },
                             [](const typename List<unsigned int>::Cons _args0)
                                 -> bool { return false; }},
                         needle->v());
                     _continue = false;
                   },
                   [&](const typename List<unsigned int>::Cons _args) {
                     if (is_prefix_of(needle, _loop_haystack)) {
                       _result = true;
                       _continue = false;
                     } else {
                       _loop_haystack = _args.d_a1;
                     }
                   }},
        _loop_haystack->v());
  }
  return _result;
}

__attribute__((pure)) bool LoopifyListRelations::is_infix_of(
    const std::shared_ptr<List<unsigned int>> &_x0,
    const std::shared_ptr<List<unsigned int>> &_x1) {
  return is_infix_of_aux(_x0, _x1);
}

std::shared_ptr<List<unsigned int>> LoopifyListRelations::find_sublists_aux(
    std::shared_ptr<List<unsigned int>> needle,
    const std::shared_ptr<List<unsigned int>> &haystack,
    const unsigned int idx) {
  struct _Enter {
    const unsigned int idx;
    const std::shared_ptr<List<unsigned int>> haystack;
    std::shared_ptr<List<unsigned int>> needle;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{idx, haystack, needle});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const unsigned int idx = _f.idx;
              const std::shared_ptr<List<unsigned int>> haystack = _f.haystack;
              std::shared_ptr<List<unsigned int>> needle = _f.needle;
              std::visit(
                  Overloaded{[&](const typename List<unsigned int>::Nil _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               _result = List<unsigned int>::ctor::Nil_();
                               return {};
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               if (is_prefix_of(needle, haystack)) {
                                 _stack.push_back(_Call1{idx});
                                 _stack.push_back(_Enter{(idx + 1u), _args.d_a1,
                                                         std::move(needle)});
                               } else {
                                 _stack.push_back(_Enter{(std::move(idx) + 1u),
                                                         _args.d_a1,
                                                         std::move(needle)});
                               }
                               return {};
                             }},
                  haystack->v());
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListRelations::find_sublists(
    const std::shared_ptr<List<unsigned int>> &needle,
    const std::shared_ptr<List<unsigned int>> &haystack) {
  return find_sublists_aux(needle, haystack, 0u);
}

__attribute__((pure)) bool
LoopifyListRelations::list_eq(const std::shared_ptr<List<unsigned int>> &l1,
                              const std::shared_ptr<List<unsigned int>> &l2) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l2;
    const std::shared_ptr<List<unsigned int>> l1;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>().d_a0 ==
             std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l2 = _f.l2;
              const std::shared_ptr<List<unsigned int>> l1 = _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> bool {
                        _result = std::visit(
                            Overloaded{
                                [](const typename List<unsigned int>::Nil
                                       _args0) -> bool { return true; },
                                [](const typename List<unsigned int>::Cons
                                       _args0) -> bool { return false; }},
                            l2->v());
                        return {};
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> bool {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0) -> bool {
                                  _result = false;
                                  return {};
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0) -> bool {
                                  _stack.push_back(
                                      _Call1{_args.d_a0 == _args0.d_a0});
                                  _stack.push_back(
                                      _Enter{_args0.d_a1, _args.d_a1});
                                  return {};
                                }},
                            l2->v());
                        return {};
                      }},
                  l1->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 && _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyListRelations::list_compare(
    const std::shared_ptr<List<unsigned int>> &l1,
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

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListRelations::zip(const std::shared_ptr<List<unsigned int>> &l1,
                          const std::shared_ptr<List<unsigned int>> &l2) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l2;
    const std::shared_ptr<List<unsigned int>> l1;
  };

  struct _Call1 {
    decltype(std::make_pair(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
        std::declval<const typename List<unsigned int>::Cons &>().d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l2 = _f.l2;
              const std::shared_ptr<List<unsigned int>> l1 = _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> std::shared_ptr<
                              List<std::pair<unsigned int, unsigned int>>> {
                        _result = List<std::pair<unsigned int,
                                                 unsigned int>>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> std::shared_ptr<
                              List<std::pair<unsigned int, unsigned int>>> {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0)
                                    -> std::shared_ptr<List<std::pair<
                                        unsigned int, unsigned int>>> {
                                  _result = List<
                                      std::pair<unsigned int,
                                                unsigned int>>::ctor::Nil_();
                                  return {};
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0)
                                    -> std::shared_ptr<List<std::pair<
                                        unsigned int, unsigned int>>> {
                                  _stack.push_back(_Call1{
                                      std::make_pair(_args.d_a0, _args0.d_a0)});
                                  _stack.push_back(
                                      _Enter{_args0.d_a1, _args.d_a1});
                                  return {};
                                }},
                            l2->v());
                        return {};
                      }},
                  l1->v());
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

std::shared_ptr<
    List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
LoopifyListRelations::zip3(const std::shared_ptr<List<unsigned int>> &l1,
                           const std::shared_ptr<List<unsigned int>> &l2,
                           const std::shared_ptr<List<unsigned int>> &l3) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l3;
    const std::shared_ptr<List<unsigned int>> l2;
    const std::shared_ptr<List<unsigned int>> l1;
  };

  struct _Call1 {
    decltype(std::make_pair(
        std::make_pair(
            std::declval<const typename List<unsigned int>::Cons &>().d_a0,
            std::declval<const typename List<unsigned int>::Cons &>().d_a0),
        std::declval<const typename List<unsigned int>::Cons &>().d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<
      List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l3, l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l3 = _f.l3;
              const std::shared_ptr<List<unsigned int>> l2 = _f.l2;
              const std::shared_ptr<List<unsigned int>> l1 = _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> std::shared_ptr<List<
                              std::pair<std::pair<unsigned int, unsigned int>,
                                        unsigned int>>> {
                        _result = List<
                            std::pair<std::pair<unsigned int, unsigned int>,
                                      unsigned int>>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> std::shared_ptr<List<
                              std::pair<std::pair<unsigned int, unsigned int>,
                                        unsigned int>>> {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0)
                                    -> std::shared_ptr<List<std::pair<
                                        std::pair<unsigned int, unsigned int>,
                                        unsigned int>>> {
                                  _result = List<std::pair<
                                      std::pair<unsigned int, unsigned int>,
                                      unsigned int>>::ctor::Nil_();
                                  return {};
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0)
                                    -> std::shared_ptr<List<std::pair<
                                        std::pair<unsigned int, unsigned int>,
                                        unsigned int>>> {
                                  std::visit(
                                      Overloaded{
                                          [&](const typename List<
                                              unsigned int>::Nil _args1)
                                              -> std::shared_ptr<List<std::pair<
                                                  std::pair<unsigned int,
                                                            unsigned int>,
                                                  unsigned int>>> {
                                            _result = List<std::pair<
                                                std::pair<unsigned int,
                                                          unsigned int>,
                                                unsigned int>>::ctor::Nil_();
                                            return {};
                                          },
                                          [&](const typename List<
                                              unsigned int>::Cons _args1)
                                              -> std::shared_ptr<List<std::pair<
                                                  std::pair<unsigned int,
                                                            unsigned int>,
                                                  unsigned int>>> {
                                            _stack.push_back(
                                                _Call1{std::make_pair(
                                                    std::make_pair(_args.d_a0,
                                                                   _args0.d_a0),
                                                    _args1.d_a0)});
                                            _stack.push_back(
                                                _Enter{_args1.d_a1, _args0.d_a1,
                                                       _args.d_a1});
                                            return {};
                                          }},
                                      l3->v());
                                  return {};
                                }},
                            l2->v());
                        return {};
                      }},
                  l1->v());
            },
            [&](_Call1 _f) {
              _result =
                  List<std::pair<std::pair<unsigned int, unsigned int>,
                                 unsigned int>>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListRelations::interleave(std::shared_ptr<List<unsigned int>> l1,
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

std::shared_ptr<List<unsigned int>>
LoopifyListRelations::merge_fuel(const unsigned int fuel,
                                 std::shared_ptr<List<unsigned int>> l1,
                                 std::shared_ptr<List<unsigned int>> l2) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l2;
    std::shared_ptr<List<unsigned int>> l1;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  struct _Call2 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l2, l1, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<List<unsigned int>> l2 = _f.l2;
              std::shared_ptr<List<unsigned int>> l1 = _f.l1;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = List<unsigned int>::ctor::Nil_();
              } else {
                unsigned int fuel_ = fuel - 1;
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
                                    _result = l1;
                                    return {};
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          _args0)
                                      -> std::shared_ptr<List<unsigned int>> {
                                    if (_args.d_a0 <= _args0.d_a0) {
                                      _stack.push_back(_Call1{_args.d_a0});
                                      _stack.push_back(
                                          _Enter{std::move(l2), _args.d_a1,
                                                 std::move(fuel_)});
                                    } else {
                                      _stack.push_back(_Call2{_args0.d_a0});
                                      _stack.push_back(_Enter{
                                          _args0.d_a1, l1, std::move(fuel_)});
                                    }
                                    return {};
                                  }},
                              l2->v());
                          return {};
                        }},
                    l1->v());
              }
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            },
            [&](_Call2 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListRelations::merge(const std::shared_ptr<List<unsigned int>> &l1,
                            const std::shared_ptr<List<unsigned int>> &l2) {
  unsigned int len1 = l1->length();
  unsigned int len2 = l2->length();
  return merge_fuel((std::move(len1) + std::move(len2)), l1, l2);
}

std::shared_ptr<List<unsigned int>>
LoopifyListRelations::union_(const std::shared_ptr<List<unsigned int>> &l1,
                             std::shared_ptr<List<unsigned int>> l2) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l2;
    const std::shared_ptr<List<unsigned int>> l1;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
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
              const std::shared_ptr<List<unsigned int>> l1 = _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        _result = std::move(l2);
                        return {};
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        if ([&](void) {
                              std::function<bool(
                                  unsigned int,
                                  std::shared_ptr<List<unsigned int>>)>
                                  member;
                              member =
                                  [&](unsigned int y,
                                      std::shared_ptr<List<unsigned int>> ys)
                                  -> bool {
                                struct _Enter {
                                  std::shared_ptr<List<unsigned int>> ys;
                                };
                                struct _Call1 {
                                  decltype(std::declval<unsigned int &>() ==
                                           std::declval<const typename List<
                                               unsigned int>::Cons &>()
                                               .d_a0) _s0;
                                };
                                using _Frame = std::variant<_Enter, _Call1>;
                                bool _result{};
                                std::vector<_Frame> _stack;
                                _stack.push_back(_Enter{ys});
                                while (!_stack.empty()) {
                                  _Frame _frame = std::move(_stack.back());
                                  _stack.pop_back();
                                  std::visit(
                                      Overloaded{
                                          [&](_Enter _f) {
                                            std::shared_ptr<List<unsigned int>>
                                                ys = _f.ys;
                                            std::visit(
                                                Overloaded{
                                                    [&](const typename List<
                                                        unsigned int>::Nil
                                                            _args) -> bool {
                                                      _result = false;
                                                      return {};
                                                    },
                                                    [&](const typename List<
                                                        unsigned int>::Cons
                                                            _args) -> bool {
                                                      _stack.push_back(_Call1{
                                                          y == _args.d_a0});
                                                      _stack.push_back(
                                                          _Enter{_args.d_a1});
                                                      return {};
                                                    }},
                                                ys->v());
                                          },
                                          [&](_Call1 _f) {
                                            _result = (_f._s0 || _result);
                                          }},
                                      _frame);
                                }
                                return _result;
                              };
                              return member(_args.d_a0, l2);
                            }()) {
                          _stack.push_back(_Enter{std::move(l2), _args.d_a1});
                        } else {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{std::move(l2), _args.d_a1});
                        }
                        return {};
                      }},
                  l1->v());
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListRelations::intersection(
    const std::shared_ptr<List<unsigned int>> &l1,
    std::shared_ptr<List<unsigned int>> l2) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l2;
    const std::shared_ptr<List<unsigned int>> l1;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
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
              const std::shared_ptr<List<unsigned int>> l1 = _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        _result = List<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        if ([&](void) {
                              std::function<bool(
                                  unsigned int,
                                  std::shared_ptr<List<unsigned int>>)>
                                  member;
                              member =
                                  [&](unsigned int y,
                                      std::shared_ptr<List<unsigned int>> ys)
                                  -> bool {
                                struct _Enter {
                                  std::shared_ptr<List<unsigned int>> ys;
                                };
                                struct _Call1 {
                                  decltype(std::declval<unsigned int &>() ==
                                           std::declval<const typename List<
                                               unsigned int>::Cons &>()
                                               .d_a0) _s0;
                                };
                                using _Frame = std::variant<_Enter, _Call1>;
                                bool _result{};
                                std::vector<_Frame> _stack;
                                _stack.push_back(_Enter{ys});
                                while (!_stack.empty()) {
                                  _Frame _frame = std::move(_stack.back());
                                  _stack.pop_back();
                                  std::visit(
                                      Overloaded{
                                          [&](_Enter _f) {
                                            std::shared_ptr<List<unsigned int>>
                                                ys = _f.ys;
                                            std::visit(
                                                Overloaded{
                                                    [&](const typename List<
                                                        unsigned int>::Nil
                                                            _args) -> bool {
                                                      _result = false;
                                                      return {};
                                                    },
                                                    [&](const typename List<
                                                        unsigned int>::Cons
                                                            _args) -> bool {
                                                      _stack.push_back(_Call1{
                                                          y == _args.d_a0});
                                                      _stack.push_back(
                                                          _Enter{_args.d_a1});
                                                      return {};
                                                    }},
                                                ys->v());
                                          },
                                          [&](_Call1 _f) {
                                            _result = (_f._s0 || _result);
                                          }},
                                      _frame);
                                }
                                return _result;
                              };
                              return member(_args.d_a0, l2);
                            }()) {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{std::move(l2), _args.d_a1});
                        } else {
                          _stack.push_back(_Enter{std::move(l2), _args.d_a1});
                        }
                        return {};
                      }},
                  l1->v());
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}
