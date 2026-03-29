#ifndef INCLUDED_LOOPIFY_FOLDS
#define INCLUDED_LOOPIFY_FOLDS

#include <memory>
#include <type_traits>
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
};

struct LoopifyFolds {
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  fold_left(F0 &&f, const unsigned int acc,
            const std::shared_ptr<List<unsigned int>> &l) {
    unsigned int _result;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    unsigned int _loop_acc = acc;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                              _result = std::move(_loop_acc);
                              _continue = false;
                            },
                            [&](const typename List<unsigned int>::Cons _args) {
                              std::shared_ptr<List<unsigned int>> _next_l =
                                  _args.d_a1;
                              unsigned int _next_acc =
                                  f(std::move(_loop_acc), _args.d_a0);
                              _loop_l = std::move(_next_l);
                              _loop_acc = std::move(_next_acc);
                            }},
                 _loop_l->v());
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  fold_right(F0 &&f, const std::shared_ptr<List<unsigned int>> &l,
             const unsigned int acc) {
    struct _Enter {
      const unsigned int acc;
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename List<unsigned int>::Cons &>()
                   .d_a0) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{acc, l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const unsigned int acc = _f.acc;
                const std::shared_ptr<List<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> void { _result = std::move(acc); },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{std::move(acc), _args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = f(_f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  scanl(F0 &&f, const unsigned int acc,
        const std::shared_ptr<List<unsigned int>> &l) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    unsigned int _loop_acc = acc;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil _args) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = List<unsigned int>::cons(
                      std::move(_loop_acc), List<unsigned int>::nil());
                } else {
                  _head = List<unsigned int>::cons(std::move(_loop_acc),
                                                   List<unsigned int>::nil());
                }
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons _args) {
                auto _cell = List<unsigned int>::cons(_loop_acc, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                unsigned int _next_acc = f(_loop_acc, _args.d_a0);
                _loop_l = std::move(_next_l);
                _loop_acc = std::move(_next_acc);
              }},
          _loop_l->v());
    }
    return _head;
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  scanr(F0 &&f, const unsigned int acc,
        const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      const unsigned int _s0;
      F0 _s1;
      const typename List<unsigned int>::Cons _s2;
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
                            -> void {
                          _result = List<unsigned int>::cons(
                              std::move(acc), List<unsigned int>::nil());
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          _stack.push_back(_Call1{acc, f, _args});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const unsigned int acc = _f._s0;
                F0 f = _f._s1;
                const typename List<unsigned int>::Cons _args = _f._s2;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args0)
                            -> void {
                          _result = List<unsigned int>::cons(
                              std::move(acc), List<unsigned int>::nil());
                        },
                        [&](const typename List<unsigned int>::Cons _args0)
                            -> void {
                          _result = List<unsigned int>::cons(
                              f(_args.d_a0, _args0.d_a0), _args0.d_a1);
                        }},
                    _result->v());
              }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F1>
  __attribute__((pure)) static unsigned int
  foldl1_fuel(const unsigned int fuel, F1 &&f,
              const std::shared_ptr<List<unsigned int>> &l) {
    unsigned int _result;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        {
          _result = 0u;
          _continue = false;
        }
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
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
                            std::shared_ptr<List<unsigned int>> _next_l =
                                List<unsigned int>::cons(
                                    f(_args.d_a0, _args0.d_a0), _args0.d_a1);
                            unsigned int _next_fuel = fuel_;
                            _loop_l = std::move(_next_l);
                            _loop_fuel = std::move(_next_fuel);
                          }},
                      _args.d_a1->v());
                }},
            _loop_l->v());
      }
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  foldl1(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    return foldl1_fuel(l->length(), f, l);
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  foldr1(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
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
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> void { _result = 0u; },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil
                                          _args0) -> void {
                                    _result = _args.d_a0;
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          _args0) -> void {
                                    _stack.push_back(_Call1{_args.d_a0});
                                    _stack.push_back(_Enter{_args.d_a1});
                                  }},
                              _args.d_a1->v());
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = f(_f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  template <
      MapsTo<std::pair<unsigned int, unsigned int>, unsigned int, unsigned int>
          F0>
  __attribute__((
      pure)) static std::pair<unsigned int, std::shared_ptr<List<unsigned int>>>
  map_accum(F0 &&f, const unsigned int acc,
            const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
      const unsigned int acc;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<unsigned int, std::shared_ptr<List<unsigned int>>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l, acc});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<unsigned int>> l = _f.l;
                const unsigned int acc = _f.acc;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> void {
                          _result = std::make_pair(std::move(acc),
                                                   List<unsigned int>::nil());
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          unsigned int acc_ = f(acc, _args.d_a0).first;
                          unsigned int y = f(acc, _args.d_a0).second;
                          _stack.push_back(_Call1{y});
                          _stack.push_back(_Enter{_args.d_a1, acc_});
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                unsigned int y = _f._s0;
                unsigned int final_acc = _result.first;
                std::shared_ptr<List<unsigned int>> ys = _result.second;
                _result =
                    std::make_pair(final_acc, List<unsigned int>::cons(y, ys));
              }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  iterate_accum(F0 &&f, const unsigned int n, const unsigned int x) {
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
                List<unsigned int>::nil();
          } else {
            _head = List<unsigned int>::nil();
          }
          _continue = false;
        }
      } else {
        unsigned int n_ = _loop_n - 1;
        {
          auto _cell = List<unsigned int>::cons(_loop_x, nullptr);
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

  template <MapsTo<std::pair<unsigned int, unsigned int>, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>>
  unfold_fuel(const unsigned int fuel, F1 &&f, const unsigned int seed) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    unsigned int _loop_seed = seed;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        {
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                List<unsigned int>::nil();
          } else {
            _head = List<unsigned int>::nil();
          }
          _continue = false;
        }
      } else {
        unsigned int fuel_ = _loop_fuel - 1;
        unsigned int x = f(_loop_seed).first;
        unsigned int next_seed = f(_loop_seed).second;
        {
          auto _cell = List<unsigned int>::cons(x, nullptr);
          if (_last) {
            std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                _cell;
          } else {
            _head = _cell;
          }
          _last = _cell;
          unsigned int _next_seed = next_seed;
          unsigned int _next_fuel = fuel_;
          _loop_seed = std::move(_next_seed);
          _loop_fuel = std::move(_next_fuel);
          continue;
        }
      }
    }
    return _head;
  }

  template <MapsTo<std::pair<unsigned int, unsigned int>, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>>
  unfold(const unsigned int _x0, F1 &&_x1, const unsigned int _x2) {
    return unfold_fuel(_x0, _x1, _x2);
  }
};

#endif // INCLUDED_LOOPIFY_FOLDS
