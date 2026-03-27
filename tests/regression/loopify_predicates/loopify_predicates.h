#ifndef INCLUDED_LOOPIFY_PREDICATES
#define INCLUDED_LOOPIFY_PREDICATES

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

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct LoopifyPredicates {
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  take_while(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
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
                if (p(_args.d_a0)) {
                  auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                  if (_last) {
                    std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  _loop_l = _args.d_a1;
                } else {
                  if (_last) {
                    std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = List<unsigned int>::nil();
                  } else {
                    _head = List<unsigned int>::nil();
                  }
                  _continue = false;
                }
              }},
          _loop_l->v());
    }
    return _head;
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  drop_while(F0 &&p, std::shared_ptr<List<unsigned int>> l) {
    struct _Enter {
      std::shared_ptr<List<unsigned int>> l;
    };

    using _Frame = std::variant<_Enter>;
    std::shared_ptr<List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
            std::shared_ptr<List<unsigned int>> l = _f.l;
            if (l.use_count() == 1 && l->v().index() == 0) {
              auto &_rf = std::get<0>(l->v_mut());
              _result = l;
            } else {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> void { _result = List<unsigned int>::nil(); },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        if (p(_args.d_a0)) {
                          _stack.push_back(_Enter{_args.d_a1});
                        } else {
                          _result = std::move(l);
                        }
                      }},
                  l->v());
            }
          }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
  span(F0 &&p, std::shared_ptr<List<unsigned int>> l) {
    struct _Enter {
      std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      const typename List<unsigned int>::Cons _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::shared_ptr<List<unsigned int>>,
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
                std::shared_ptr<List<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> void {
                          _result = std::make_pair(List<unsigned int>::nil(),
                                                   List<unsigned int>::nil());
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          if (p(_args.d_a0)) {
                            _stack.push_back(_Call1{_args});
                            _stack.push_back(_Enter{_args.d_a1});
                          } else {
                            _result = std::make_pair(List<unsigned int>::nil(),
                                                     std::move(l));
                          }
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<unsigned int>::Cons _args = _f._s0;
                std::shared_ptr<List<unsigned int>> yes = _result.first;
                std::shared_ptr<List<unsigned int>> no = _result.second;
                _result = std::make_pair(
                    List<unsigned int>::cons(_args.d_a0, yes), no);
              }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
  break_at(F0 &&p, std::shared_ptr<List<unsigned int>> l) {
    struct _Enter {
      std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      const typename List<unsigned int>::Cons _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::shared_ptr<List<unsigned int>>,
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
                std::shared_ptr<List<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> void {
                          _result = std::make_pair(List<unsigned int>::nil(),
                                                   List<unsigned int>::nil());
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          if (p(_args.d_a0)) {
                            _result = std::make_pair(List<unsigned int>::nil(),
                                                     std::move(l));
                          } else {
                            _stack.push_back(_Call1{_args});
                            _stack.push_back(_Enter{_args.d_a1});
                          }
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<unsigned int>::Cons _args = _f._s0;
                std::shared_ptr<List<unsigned int>> before = _result.first;
                std::shared_ptr<List<unsigned int>> after = _result.second;
                _result = std::make_pair(
                    List<unsigned int>::cons(_args.d_a0, before), after);
              }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  filter(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
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
                if (p(_args.d_a0)) {
                  auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                  if (_last) {
                    std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  _loop_l = _args.d_a1;
                } else {
                  _loop_l = _args.d_a1;
                }
              }},
          _loop_l->v());
    }
    return _head;
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  reject(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
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
                if (p(_args.d_a0)) {
                  _loop_l = _args.d_a1;
                } else {
                  auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                  if (_last) {
                    std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  _loop_l = _args.d_a1;
                }
              }},
          _loop_l->v());
    }
    return _head;
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool
  forall_pred(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      bool _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    bool _result{};
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
                            -> void { _result = true; },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          _stack.push_back(_Call1{p(_args.d_a0)});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = (_f._s0 && _result); }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool
  exists_pred(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      bool _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    bool _result{};
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
                            -> void { _result = false; },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          _stack.push_back(_Call1{p(_args.d_a0)});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = (_f._s0 || _result); }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::optional<unsigned int>
  find_index_aux(F0 &&p, const std::shared_ptr<List<unsigned int>> &l,
                 const unsigned int idx) {
    std::optional<unsigned int> _result;
    unsigned int _loop_idx = idx;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                              _result = std::optional<unsigned int>();
                              _continue = false;
                            },
                            [&](const typename List<unsigned int>::Cons _args) {
                              if (p(_args.d_a0)) {
                                _result = std::make_optional<unsigned int>(
                                    std::move(_loop_idx));
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

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static std::optional<unsigned int>
  find_index(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    return find_index_aux(p, l, 0u);
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  find_indices_aux(F0 &&p, const std::shared_ptr<List<unsigned int>> &l,
                   const unsigned int idx) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    unsigned int _loop_idx = idx;
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
                if (p(_args.d_a0)) {
                  auto _cell = List<unsigned int>::cons(_loop_idx, nullptr);
                  if (_last) {
                    std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  unsigned int _next_idx = (_loop_idx + 1u);
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  _loop_idx = std::move(_next_idx);
                  _loop_l = std::move(_next_l);
                } else {
                  unsigned int _next_idx = (std::move(_loop_idx) + 1u);
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  _loop_idx = std::move(_next_idx);
                  _loop_l = std::move(_next_l);
                }
              }},
          _loop_l->v());
    }
    return _head;
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  find_indices(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    return find_indices_aux(p, l, 0u);
  }

  template <MapsTo<bool, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  delete_by(F0 &&eq, const unsigned int x,
            const std::shared_ptr<List<unsigned int>> &l) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    unsigned int _loop_x = x;
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
                if (eq(_loop_x, _args.d_a0)) {
                  if (_last) {
                    std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = _args.d_a1;
                  } else {
                    _head = _args.d_a1;
                  }
                  _continue = false;
                } else {
                  auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                  if (_last) {
                    std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  unsigned int _next_x = std::move(_loop_x);
                  _loop_l = std::move(_next_l);
                  _loop_x = std::move(_next_x);
                }
              }},
          _loop_l->v());
    }
    return _head;
  }

  static std::shared_ptr<List<unsigned int>>
  remove_all(const unsigned int x,
             const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_PREDICATES
