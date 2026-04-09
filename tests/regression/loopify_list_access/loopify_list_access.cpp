#include <loopify_list_access.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
LoopifyListAccess::nth(const unsigned int n,
                       const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                     _result = 0u;
                     _continue = false;
                   },
                   [&](const typename List<unsigned int>::Cons _args) {
                     if (_loop_n == 0u) {
                       _result = _args.d_a0;
                       _continue = false;
                     } else {
                       std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                       unsigned int _next_n =
                           (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
                       _loop_l = std::move(_next_l);
                       _loop_n = std::move(_next_n);
                     }
                   }},
        _loop_l->v());
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyListAccess::last(const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              _result = 0u;
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args0) {
                        _result = _args.d_a0;
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
                        _loop_l = _args.d_a1;
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyListAccess::index_of_aux(const unsigned int x,
                                const std::shared_ptr<List<unsigned int>> &l,
                                const unsigned int idx) {
  unsigned int _result;
  unsigned int _loop_idx = idx;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                            _result = 0u;
                            _continue = false;
                          },
                          [&](const typename List<unsigned int>::Cons _args) {
                            if (x == _args.d_a0) {
                              _result = std::move(_loop_idx);
                              _continue = false;
                            } else {
                              unsigned int _next_idx =
                                  (std::move(_loop_idx) + 1u);
                              std::shared_ptr<List<unsigned int>> _next_l =
                                  _args.d_a1;
                              _loop_idx = std::move(_next_idx);
                              _loop_l = std::move(_next_l);
                            }
                          }},
               _loop_l->v());
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyListAccess::index_of(const unsigned int x,
                            const std::shared_ptr<List<unsigned int>> &l) {
  return index_of_aux(x, l, 0u);
}

__attribute__((pure)) bool
LoopifyListAccess::member(const unsigned int x,
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

__attribute__((pure)) unsigned int LoopifyListAccess::lookup(
    const unsigned int key,
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l) {
  unsigned int _result;
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<std::pair<unsigned int, unsigned int>>::Nil
                    _args) {
              _result = 0u;
              _continue = false;
            },
            [&](const typename List<std::pair<unsigned int, unsigned int>>::Cons
                    _args) {
              unsigned int k = _args.d_a0.first;
              unsigned int v = _args.d_a0.second;
              if (k == key) {
                _result = v;
                _continue = false;
              } else {
                _loop_l = _args.d_a1;
              }
            }},
        _loop_l->v());
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListAccess::lookup_all(
    const unsigned int key,
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _loop_l = l;
  unsigned int _loop_key = key;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<std::pair<unsigned int, unsigned int>>::Nil
                    _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<std::pair<unsigned int, unsigned int>>::Cons
                    _args) {
              unsigned int k = _args.d_a0.first;
              unsigned int v = _args.d_a0.second;
              if (k == _loop_key) {
                auto _cell = List<unsigned int>::cons(v, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_l = _args.d_a1;
              } else {
                std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
                    _next_l = _args.d_a1;
                unsigned int _next_key = std::move(_loop_key);
                _loop_l = std::move(_next_l);
                _loop_key = std::move(_next_key);
              }
            }},
        _loop_l->v());
  }
  return _head;
}

__attribute__((pure)) unsigned int
LoopifyListAccess::count(const unsigned int x,
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

__attribute__((pure)) bool
LoopifyListAccess::elem_at_eq(const unsigned int idx, const unsigned int val,
                              const std::shared_ptr<List<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_idx = idx;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                     _result = false;
                     _continue = false;
                   },
                   [&](const typename List<unsigned int>::Cons _args) {
                     if (_loop_idx == 0u) {
                       _result = _args.d_a0 == val;
                       _continue = false;
                     } else {
                       std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                       unsigned int _next_idx =
                           (((_loop_idx - 1u) > _loop_idx ? 0
                                                          : (_loop_idx - 1u)));
                       _loop_l = std::move(_next_l);
                       _loop_idx = std::move(_next_idx);
                     }
                   }},
        _loop_l->v());
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyListAccess::nth_default(const unsigned int n,
                               const unsigned int default0,
                               const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_default0 = default0;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                     _result = std::move(_loop_default0);
                     _continue = false;
                   },
                   [&](const typename List<unsigned int>::Cons _args) {
                     if (_loop_n == 0u) {
                       _result = _args.d_a0;
                       _continue = false;
                     } else {
                       std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                       unsigned int _next_default0 = std::move(_loop_default0);
                       unsigned int _next_n =
                           (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
                       _loop_l = std::move(_next_l);
                       _loop_default0 = std::move(_next_default0);
                       _loop_n = std::move(_next_n);
                     }
                   }},
        _loop_l->v());
  }
  return _result;
}
