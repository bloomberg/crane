#ifndef INCLUDED_LOOPIFY_GENERATORS
#define INCLUDED_LOOPIFY_GENERATORS

#include <functional>
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
                auto _cell = List<t_A>::cons(_args.d_a0, nullptr);
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

struct Nat {
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int x, const unsigned int y, const unsigned int q,
         const unsigned int u);
  __attribute__((pure)) static unsigned int div(const unsigned int x,
                                                const unsigned int y);
};

/// Consolidated list generator functions.
struct LoopifyGenerators {
  /// cycle n l repeats the list n times: cycle 2 1,2 -> 1,2,1,2.
  static std::shared_ptr<List<unsigned int>>
  cycle(const unsigned int n, const std::shared_ptr<List<unsigned int>> &l);

  /// iterate f n x applies f repeatedly n times: iterate (+1) 3 5 -> 5,6,7.
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
                List<unsigned int>::nil();
          } else {
            _head = List<unsigned int>::nil();
          }
          _continue = false;
        }
      } else {
        unsigned int m = _loop_n - 1;
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
          unsigned int _next_n = std::move(m);
          _loop_x = std::move(_next_x);
          _loop_n = std::move(_next_n);
          continue;
        }
      }
    }
    return _head;
  }

  /// zip_with f l1 l2 zips with a combining function.
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
                                .d_a1 = List<unsigned int>::nil();
                          } else {
                            _head = List<unsigned int>::nil();
                          }
                          _continue = false;
                        },
                        [&](const typename List<unsigned int>::Cons _args0) {
                          auto _cell = List<unsigned int>::cons(
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

  /// zip_longest l1 l2 default zips, using default for missing elements.
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  zip_longest_aux(const std::shared_ptr<List<unsigned int>> &l1,
                  const std::shared_ptr<List<unsigned int>> &l2,
                  const unsigned int default0, const unsigned int fuel);
  __attribute__((pure)) static unsigned int
  len_impl(const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  zip_longest(
      const std::shared_ptr<List<unsigned int>> &l1,
      const std::shared_ptr<List<unsigned int>> &l2,
      const unsigned int default0); /// build_list n builds tree-like list
                                    /// structure: build_list(4) -> 2,4,2.
  static std::shared_ptr<List<unsigned int>>
  build_list_fuel(const unsigned int fuel, const unsigned int n);
  static std::shared_ptr<List<unsigned int>> build_list(const unsigned int n);
  /// take n l returns first n elements.
  static std::shared_ptr<List<unsigned int>>
  take(const unsigned int n, const std::shared_ptr<List<unsigned int>> &l);
  /// repeat x n creates list with n copies of x.
  static std::shared_ptr<List<unsigned int>> repeat(const unsigned int x,
                                                    const unsigned int n);

  /// unfold f n init unfolds a list from seed value.
  template <MapsTo<std::pair<unsigned int, unsigned int>, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>>
  unfold_fuel(const unsigned int fuel, F1 &&f, const unsigned int n,
              const unsigned int seed) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    unsigned int _loop_seed = seed;
    unsigned int _loop_n = n;
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
        unsigned int g = _loop_fuel - 1;
        if (_loop_n == 0u) {
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
          unsigned int val = f(_loop_seed).first;
          unsigned int next_seed = f(_loop_seed).second;
          {
            auto _cell = List<unsigned int>::cons(std::move(val), nullptr);
            if (_last) {
              std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
                  _cell;
            } else {
              _head = _cell;
            }
            _last = _cell;
            unsigned int _next_seed = next_seed;
            unsigned int _next_n =
                (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
            unsigned int _next_fuel = g;
            _loop_seed = std::move(_next_seed);
            _loop_n = std::move(_next_n);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
    return _head;
  }

  template <MapsTo<std::pair<unsigned int, unsigned int>, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  unfold(F0 &&f, const unsigned int n, const unsigned int seed) {
    return unfold_fuel(100u, f, n, seed);
  }

  /// tabulate n f generates f 0, f 1, ..., f (n-1) (same as init_list but
  /// different naming).
  template <MapsTo<unsigned int, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>> tabulate(const unsigned int n,
                                                      F1 &&f) {
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
        std::visit(Overloaded{[&](_Enter _f) {
                                unsigned int i = _f.i;
                                if (i <= 0) {
                                  _result = List<unsigned int>::nil();
                                } else {
                                  unsigned int j = i - 1;
                                  _stack.push_back(
                                      _Call1{f((((n - i) > n ? 0 : (n - i))))});
                                  _stack.push_back(_Enter{std::move(j)});
                                }
                              },
                              [&](_Call1 _f) {
                                _result =
                                    List<unsigned int>::cons(_f._s0, _result);
                              }},
                   _frame);
      }
      return _result;
    };
    return go(n);
  }

  /// Helper: replicate single element n times.
  static std::shared_ptr<List<unsigned int>>
  replicate_single(const unsigned int x, const unsigned int n);
  /// replicate_each n l replicates each element n times: replicate_each 2 1,2
  /// -> 1,1,2,2.
  static std::shared_ptr<List<unsigned int>>
  replicate_each(const unsigned int n,
                 const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_GENERATORS
