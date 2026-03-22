#ifndef INCLUDED_LOOPIFY_GENERATORS
#define INCLUDED_LOOPIFY_GENERATORS

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
          Overloaded{
              [&](_Enter _f) {
                const List *_self = _f._self;
                std::shared_ptr<List<t_A>> m = _f.m;
                std::visit(
                    Overloaded{
                        [&](const typename List<t_A>::Nil _args) -> void {
                          _result = m;
                        },
                        [&](const typename List<t_A>::Cons _args) -> void {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{m.get(), _args.d_a1});
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
                                unsigned int m = n - 1;
                                _stack.push_back(_Call1{x});
                                _stack.push_back(_Enter{f(x), std::move(m)});
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

  /// zip_with f l1 l2 zips with a combining function.
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
                            -> void {
                          _result = List<unsigned int>::ctor::Nil_();
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil
                                          _args0) -> void {
                                    _result = List<unsigned int>::ctor::Nil_();
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          _args0) -> void {
                                    _stack.push_back(
                                        _Call1{f(_args.d_a0, _args0.d_a0)});
                                    _stack.push_back(
                                        _Enter{_args0.d_a1, _args.d_a1});
                                  }},
                              l2->v());
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
    struct _Enter {
      const unsigned int seed;
      const unsigned int n;
      const unsigned int fuel;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{seed, n, fuel});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
                       const unsigned int seed = _f.seed;
                       const unsigned int n = _f.n;
                       const unsigned int fuel = _f.fuel;
                       if (fuel <= 0) {
                         _result = List<unsigned int>::ctor::Nil_();
                       } else {
                         unsigned int g = fuel - 1;
                         if (n == 0u) {
                           _result = List<unsigned int>::ctor::Nil_();
                         } else {
                           unsigned int val = f(seed).first;
                           unsigned int next_seed = f(seed).second;
                           _stack.push_back(_Call1{std::move(val)});
                           _stack.push_back(_Enter{
                               next_seed, (((n - 1u) > n ? 0 : (n - 1u))), g});
                         }
                       }
                     },
                     [&](_Call1 _f) {
                       _result =
                           List<unsigned int>::ctor::Cons_(_f._s0, _result);
                     }},
          _frame);
    }
    return _result;
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
                                  _result = List<unsigned int>::ctor::Nil_();
                                } else {
                                  unsigned int j = i - 1;
                                  _stack.push_back(
                                      _Call1{f((((n - i) > n ? 0 : (n - i))))});
                                  _stack.push_back(_Enter{std::move(j)});
                                }
                              },
                              [&](_Call1 _f) {
                                _result = List<unsigned int>::ctor::Cons_(
                                    _f._s0, _result);
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
