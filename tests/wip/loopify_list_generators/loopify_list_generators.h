#ifndef INCLUDED_LOOPIFY_LIST_GENERATORS
#define INCLUDED_LOOPIFY_LIST_GENERATORS

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

  __attribute__((pure)) unsigned int length() const {
    const List *_self = this;

    struct _Enter {
      const List *_self;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{_self});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
                       const List *_self = _f._self;
                       std::visit(
                           Overloaded{[&](const typename List<t_A>::Nil _args)
                                          -> unsigned int {
                                        _result = 0u;
                                        return {};
                                      },
                                      [&](const typename List<t_A>::Cons _args)
                                          -> unsigned int {
                                        _stack.push_back(_Call1{});
                                        _stack.push_back(
                                            _Enter{_args.d_a1.get()});
                                        return {};
                                      }},
                           _self->v());
                     },
                     [&](_Call1 _f) { _result = (_result + 1); }},
          _frame);
    }
    return _result;
  }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    const List *_self = this;

    struct _Enter {
      const List *_self;
      std::shared_ptr<List<t_A>> m;
    };

    struct _Call1 {
      decltype(std::declval<const typename List<t_A>::Cons &>().d_a0) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<t_A>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{_self, m});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
                       const List *_self = _f._self;
                       std::shared_ptr<List<t_A>> m = _f.m;
                       std::visit(
                           Overloaded{[&](const typename List<t_A>::Nil _args)
                                          -> std::shared_ptr<List<t_A>> {
                                        _result = m;
                                        return {};
                                      },
                                      [&](const typename List<t_A>::Cons _args)
                                          -> std::shared_ptr<List<t_A>> {
                                        _stack.push_back(_Call1{_args.d_a0});
                                        _stack.push_back(
                                            _Enter{m.get(), _args.d_a1});
                                        return {};
                                      }},
                           _self->v());
                     },
                     [&](_Call1 _f) {
                       _result = List<t_A>::ctor::Cons_(_f._s0, _result);
                     }},
          _frame);
    }
    return _result;
  }
};

struct LoopifyListGenerators {
  static std::shared_ptr<List<unsigned int>>
  cycle_fuel(const unsigned int fuel, const unsigned int n,
             const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  cycle(const unsigned int n, const std::shared_ptr<List<unsigned int>> &l);

  template <MapsTo<unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  iterate(F0 &&f, const unsigned int n, const unsigned int x) {
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
                                _stack.push_back(_Enter{f(x), std::move(n_)});
                              }
                            },
                            [&](_Call1 _f) {
                              _result = List<unsigned int>::ctor::Cons_(
                                  _f._s0, _result);
                            }},
                 _frame);
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int> F2>
  static std::shared_ptr<List<unsigned int>>
  build_list_aux(const unsigned int n, const unsigned int idx, F2 &&f) {
    struct _Enter {
      const unsigned int idx;
      const unsigned int n;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{idx, n});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(Overloaded{[&](_Enter _f) {
                              const unsigned int idx = _f.idx;
                              const unsigned int n = _f.n;
                              if (n <= 0) {
                                _result = List<unsigned int>::ctor::Nil_();
                              } else {
                                unsigned int n_ = n - 1;
                                _stack.push_back(_Call1{f(idx)});
                                _stack.push_back(_Enter{(idx + 1u), n_});
                              }
                            },
                            [&](_Call1 _f) {
                              _result = List<unsigned int>::ctor::Cons_(
                                  _f._s0, _result);
                            }},
                 _frame);
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>> build_list(const unsigned int n,
                                                        F1 &&f) {
    return build_list_aux(n, 0u, f);
  }

  template <MapsTo<unsigned int, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>> init_list(const unsigned int n,
                                                       F1 &&f) {
    if (n <= 0) {
      return List<unsigned int>::ctor::Nil_();
    } else {
      unsigned int n_ = n - 1;
      return List<unsigned int>::ctor::Cons_(f(0u), [&](void) {
        std::function<std::shared_ptr<List<unsigned int>>(unsigned int)> go;
        go = [&](unsigned int i) -> std::shared_ptr<List<unsigned int>> {
          struct _Enter {
            unsigned int i;
          };
          struct _Call1 {
            decltype(f((((n - std::declval<unsigned int &>()) > n
                             ? 0
                             : (n - std::declval<unsigned int &>()))))) _s0;
          };
          using _Frame = std::variant<_Enter, _Call1>;
          std::shared_ptr<List<unsigned int>> _result{};
          std::vector<_Frame> _stack;
          _stack.push_back(_Enter{i});
          while (!_stack.empty()) {
            _Frame _frame = std::move(_stack.back());
            _stack.pop_back();
            std::visit(
                Overloaded{[&](_Enter _f) {
                             unsigned int i = _f.i;
                             if (i <= 0) {
                               _result = List<unsigned int>::ctor::Nil_();
                             } else {
                               unsigned int i_ = i - 1;
                               _stack.push_back(
                                   _Call1{f((((n - i) > n ? 0 : (n - i))))});
                               _stack.push_back(_Enter{std::move(i_)});
                             }
                           },
                           [&](_Call1 _f) {
                             _result = List<unsigned int>::ctor::Cons_(_f._s0,
                                                                       _result);
                           }},
                _frame);
          }
          return _result;
        };
        return go(n_);
      }());
    }
  }

  static std::shared_ptr<List<unsigned int>> range(const unsigned int start,
                                                   const unsigned int count);
  static std::shared_ptr<List<unsigned int>>
  replicate_elem(const unsigned int n, const unsigned int x);
  static std::shared_ptr<List<unsigned int>>
  replicate_each(const unsigned int n,
                 const std::shared_ptr<List<unsigned int>> &l);

  template <MapsTo<unsigned int, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>> tabulate(const unsigned int n,
                                                      F1 &&f) {
    if (n <= 0) {
      return List<unsigned int>::ctor::Nil_();
    } else {
      unsigned int n_ = n - 1;
      std::function<std::shared_ptr<List<unsigned int>>(unsigned int)> aux;
      aux = [&](unsigned int idx) -> std::shared_ptr<List<unsigned int>> {
        struct _Enter {
          unsigned int idx;
        };
        struct _Call1 {
          decltype(List<unsigned int>::ctor::Cons_(
              f(std::declval<unsigned int &>()),
              List<unsigned int>::ctor::Nil_())) _s0;
        };
        using _Frame = std::variant<_Enter, _Call1>;
        std::shared_ptr<List<unsigned int>> _result{};
        std::vector<_Frame> _stack;
        _stack.push_back(_Enter{idx});
        while (!_stack.empty()) {
          _Frame _frame = std::move(_stack.back());
          _stack.pop_back();
          std::visit(
              Overloaded{
                  [&](_Enter _f) {
                    unsigned int idx = _f.idx;
                    if (idx <= 0) {
                      _result = List<unsigned int>::ctor::Cons_(
                          f(0u), List<unsigned int>::ctor::Nil_());
                    } else {
                      unsigned int idx_ = idx - 1;
                      _stack.push_back(_Call1{List<unsigned int>::ctor::Cons_(
                          f(idx), List<unsigned int>::ctor::Nil_())});
                      _stack.push_back(_Enter{std::move(idx_)});
                    }
                  },
                  [&](_Call1 _f) { _result = _result->app(_f._s0); }},
              _frame);
        }
        return _result;
      };
      return aux(n_);
    }
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  zip_with(F0 &&f, const std::shared_ptr<List<unsigned int>> &l1,
           const std::shared_ptr<List<unsigned int>> &l2) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l2;
      const std::shared_ptr<List<unsigned int>> l1;
    };

    struct _Call1 {
      unsigned int _s0;
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
                const std::shared_ptr<List<unsigned int>> l2 = _f.l2;
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
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil
                                          _args0)
                                      -> std::shared_ptr<List<unsigned int>> {
                                    _result = List<unsigned int>::ctor::Nil_();
                                    return {};
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          _args0)
                                      -> std::shared_ptr<List<unsigned int>> {
                                    _stack.push_back(
                                        _Call1{f(_args.d_a0, _args0.d_a0)});
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
                _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
              }},
          _frame);
    }
    return _result;
  }

  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  enumerate_aux(const unsigned int idx,
                const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  enumerate(const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_LIST_GENERATORS
