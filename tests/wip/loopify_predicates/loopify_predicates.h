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

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct LoopifyPredicates {
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  take_while(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename List<unsigned int>::Cons &>()
                   .d_a0) _s0;
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
                          if (p(_args.d_a0)) {
                            _stack.push_back(_Call1{_args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1});
                          } else {
                            _result = List<unsigned int>::ctor::Nil_();
                          }
                          return {};
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
                  Overloaded{[&](const typename List<unsigned int>::Nil _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               _result = List<unsigned int>::ctor::Nil_();
                               return {};
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               if (p(_args.d_a0)) {
                                 _stack.push_back(_Enter{_args.d_a1});
                               } else {
                                 _result = std::move(l);
                               }
                               return {};
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
                            -> std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>> {
                          _result =
                              std::make_pair(List<unsigned int>::ctor::Nil_(),
                                             List<unsigned int>::ctor::Nil_());
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>> {
                          if (p(_args.d_a0)) {
                            _stack.push_back(_Call1{_args});
                            _stack.push_back(_Enter{_args.d_a1});
                          } else {
                            _result = std::make_pair(
                                List<unsigned int>::ctor::Nil_(), std::move(l));
                          }
                          return {};
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<unsigned int>::Cons _args = _f._s0;
                std::shared_ptr<List<unsigned int>> yes = _result.first;
                std::shared_ptr<List<unsigned int>> no = _result.second;
                _result = std::make_pair(
                    List<unsigned int>::ctor::Cons_(_args.d_a0, yes), no);
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
                            -> std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>> {
                          _result =
                              std::make_pair(List<unsigned int>::ctor::Nil_(),
                                             List<unsigned int>::ctor::Nil_());
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>> {
                          if (p(_args.d_a0)) {
                            _result = std::make_pair(
                                List<unsigned int>::ctor::Nil_(), std::move(l));
                          } else {
                            _stack.push_back(_Call1{_args});
                            _stack.push_back(_Enter{_args.d_a1});
                          }
                          return {};
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<unsigned int>::Cons _args = _f._s0;
                std::shared_ptr<List<unsigned int>> before = _result.first;
                std::shared_ptr<List<unsigned int>> after = _result.second;
                _result = std::make_pair(
                    List<unsigned int>::ctor::Cons_(_args.d_a0, before), after);
              }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  filter(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename List<unsigned int>::Cons &>()
                   .d_a0) _s0;
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
                          if (p(_args.d_a0)) {
                            _stack.push_back(_Call1{_args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1});
                          } else {
                            _stack.push_back(_Enter{_args.d_a1});
                          }
                          return {};
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

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  reject(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename List<unsigned int>::Cons &>()
                   .d_a0) _s0;
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
                          if (p(_args.d_a0)) {
                            _stack.push_back(_Enter{_args.d_a1});
                          } else {
                            _stack.push_back(_Call1{_args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1});
                          }
                          return {};
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
                            -> bool {
                          _result = true;
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> bool {
                          _stack.push_back(_Call1{p(_args.d_a0)});
                          _stack.push_back(_Enter{_args.d_a1});
                          return {};
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
                            -> bool {
                          _result = false;
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> bool {
                          _stack.push_back(_Call1{p(_args.d_a0)});
                          _stack.push_back(_Enter{_args.d_a1});
                          return {};
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
                              _result = std::nullopt;
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
    struct _Enter {
      const unsigned int idx;
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      const unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{idx, l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const unsigned int idx = _f.idx;
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
                          if (p(_args.d_a0)) {
                            _stack.push_back(_Call1{idx});
                            _stack.push_back(_Enter{(idx + 1u), _args.d_a1});
                          } else {
                            _stack.push_back(
                                _Enter{(std::move(idx) + 1u), _args.d_a1});
                          }
                          return {};
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

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  find_indices(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    return find_indices_aux(p, l, 0u);
  }

  template <MapsTo<bool, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  delete_by(F0 &&eq, const unsigned int x,
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
                            -> std::shared_ptr<List<unsigned int>> {
                          _result = List<unsigned int>::ctor::Nil_();
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> std::shared_ptr<List<unsigned int>> {
                          if (eq(x, _args.d_a0)) {
                            _result = _args.d_a1;
                          } else {
                            _stack.push_back(_Call1{_args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1, std::move(x)});
                          }
                          return {};
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

  static std::shared_ptr<List<unsigned int>>
  remove_all(const unsigned int x,
             const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_PREDICATES
