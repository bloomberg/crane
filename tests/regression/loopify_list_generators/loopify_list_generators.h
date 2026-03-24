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
          Overloaded{
              [&](_Enter _f) {
                const List *_self = _f._self;
                std::visit(
                    Overloaded{
                        [&](const typename List<t_A>::Nil _args) -> void {
                          _result = 0u;
                        },
                        [&](const typename List<t_A>::Cons _args) -> void {
                          _stack.push_back(_Call1{});
                          _stack.push_back(_Enter{_args.d_a1.get()});
                        }},
                    _self->v());
              },
              [&](_Call1 _f) { _result = (_result + 1); }},
          _frame);
    }
    return _result;
  }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    std::shared_ptr<List<t_A>> _head{};
    std::shared_ptr<List<t_A>> _last{};
    const List *_loop_self = this;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<t_A>::Nil _args) {
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = m;
                } else {
                  _head = m;
                }
                _continue = false;
              },
              [&](const typename List<t_A>::Cons _args) {
                auto _cell = List<t_A>::ctor::Cons_(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 =
                      _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_self = _args.d_a1.get();
              }},
          _loop_self->v());
    }
    return _head;
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
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    unsigned int _loop_x = x;
    unsigned int _loop_n = n;
    bool _continue = true;
    while (_continue) {
      if (_loop_n <= 0) {
        {
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                List<unsigned int>::ctor::Nil_();
          } else {
            _head = List<unsigned int>::ctor::Nil_();
          }
          _continue = false;
        }
      } else {
        unsigned int n_ = _loop_n - 1;
        {
          auto _cell = List<unsigned int>::ctor::Cons_(_loop_x, nullptr);
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          unsigned int _next_x = f(_loop_x);
          unsigned int _next_n = std::move(n_);
          _loop_x = std::move(_next_x);
          _loop_n = std::move(_next_n);
          continue;
        }
      }
    }
    return _head;
  }

  template <MapsTo<unsigned int, unsigned int> F2>
  static std::shared_ptr<List<unsigned int>>
  build_list_aux(const unsigned int n, const unsigned int idx, F2 &&f) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    unsigned int _loop_idx = idx;
    unsigned int _loop_n = n;
    bool _continue = true;
    while (_continue) {
      if (_loop_n <= 0) {
        {
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                List<unsigned int>::ctor::Nil_();
          } else {
            _head = List<unsigned int>::ctor::Nil_();
          }
          _continue = false;
        }
      } else {
        unsigned int n_ = _loop_n - 1;
        {
          auto _cell = List<unsigned int>::ctor::Cons_(f(_loop_idx), nullptr);
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          unsigned int _next_idx = (_loop_idx + 1u);
          unsigned int _next_n = n_;
          _loop_idx = std::move(_next_idx);
          _loop_n = std::move(_next_n);
          continue;
        }
      }
    }
    return _head;
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
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
    std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
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
                              f(_args.d_a0, _args0.d_a0), nullptr);
                          if (_last) {
                            std::get<typename List<unsigned int>::Cons>(
                                _last->v_mut())
                                .d_a1 = _cell;
                          } else {
                            _head = _cell;
                          }
                          _last = _cell;
                          std::shared_ptr<List<unsigned int>> _next_l2 =
                              _args0.d_a1;
                          std::shared_ptr<List<unsigned int>> _next_l1 =
                              _args.d_a1;
                          _loop_l2 = std::move(_next_l2);
                          _loop_l1 = std::move(_next_l1);
                        }},
                    _loop_l2->v());
              }},
          _loop_l1->v());
    }
    return _head;
  }

  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  enumerate_aux(const unsigned int idx,
                const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  enumerate(const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_LIST_GENERATORS
