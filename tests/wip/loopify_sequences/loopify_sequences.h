#ifndef INCLUDED_LOOPIFY_SEQUENCES
#define INCLUDED_LOOPIFY_SEQUENCES

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

struct Nat {
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int x, const unsigned int y, const unsigned int q,
         const unsigned int u);
  __attribute__((pure)) static unsigned int div(const unsigned int x,
                                                const unsigned int y);
};

struct LoopifySequences {
  /// alternate_sum sign acc l alternating sum with sign flip.
  __attribute__((pure)) static unsigned int
  alternate_sum(const unsigned int sign, const unsigned int acc,
                const std::shared_ptr<List<unsigned int>> &l);

  /// intercalate sep lists inserts sep between lists and flattens.
  template <typename T1>
  static std::shared_ptr<List<T1>>
  intercalate(const std::shared_ptr<List<T1>> &sep,
              const std::shared_ptr<List<std::shared_ptr<List<T1>>>> &lists) {
    struct _Enter {
      const std::shared_ptr<List<std::shared_ptr<List<T1>>>> lists;
    };

    struct _Call1 {
      decltype(std::declval<
                   const typename List<std::shared_ptr<List<T1>>>::Cons &>()
                   .d_a0) _s0;
      const std::shared_ptr<List<T1>> _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<T1>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{lists});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<std::shared_ptr<List<T1>>>> lists =
                    _f.lists;
                std::visit(
                    Overloaded{
                        [&](const typename List<std::shared_ptr<List<T1>>>::Nil
                                _args) -> std::shared_ptr<List<T1>> {
                          _result = List<T1>::ctor::Nil_();
                          return {};
                        },
                        [&](const typename List<std::shared_ptr<List<T1>>>::Cons
                                _args) -> std::shared_ptr<List<T1>> {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<
                                      std::shared_ptr<List<T1>>>::Nil _args0)
                                      -> std::shared_ptr<List<T1>> {
                                    _result = _args.d_a0;
                                    return {};
                                  },
                                  [&](const typename List<
                                      std::shared_ptr<List<T1>>>::Cons _args0)
                                      -> std::shared_ptr<List<T1>> {
                                    _stack.push_back(_Call1{_args.d_a0, sep});
                                    _stack.push_back(_Enter{_args.d_a1});
                                    return {};
                                  }},
                              _args.d_a1->v());
                          return {};
                        }},
                    lists->v());
              },
              [&](_Call1 _f) { _result = _f._s0->app(_f._s1->app(_result)); }},
          _frame);
    }
    return _result;
  }

  /// join_with sep l joins list elements with separator.
  template <typename T1>
  static std::shared_ptr<List<T1>>
  join_with(const T1 sep, const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{
            [](const typename List<T1>::Nil _args)
                -> std::shared_ptr<List<T1>> { return List<T1>::ctor::Nil_(); },
            [&](const typename List<T1>::Cons _args)
                -> std::shared_ptr<List<T1>> {
              std::function<std::shared_ptr<List<T1>>(
                  std::shared_ptr<List<T1>>)>
                  go;
              go = [&](std::shared_ptr<List<T1>> rest)
                  -> std::shared_ptr<List<T1>> {
                struct _Enter {
                  std::shared_ptr<List<T1>> rest;
                };
                struct _Call1 {
                  decltype(sep) _s0;
                  decltype(std::declval<const typename List<T1>::Cons &>()
                               .d_a0) _s1;
                };
                using _Frame = std::variant<_Enter, _Call1>;
                std::shared_ptr<List<T1>> _result{};
                std::vector<_Frame> _stack;
                _stack.push_back(_Enter{rest});
                while (!_stack.empty()) {
                  _Frame _frame = std::move(_stack.back());
                  _stack.pop_back();
                  std::visit(
                      Overloaded{
                          [&](_Enter _f) {
                            std::shared_ptr<List<T1>> rest = _f.rest;
                            std::visit(
                                Overloaded{
                                    [&](const typename List<T1>::Nil _args0)
                                        -> std::shared_ptr<List<T1>> {
                                      _result = List<T1>::ctor::Nil_();
                                      return {};
                                    },
                                    [&](const typename List<T1>::Cons _args0)
                                        -> std::shared_ptr<List<T1>> {
                                      _stack.push_back(
                                          _Call1{sep, _args0.d_a0});
                                      _stack.push_back(_Enter{_args0.d_a1});
                                      return {};
                                    }},
                                rest->v());
                          },
                          [&](_Call1 _f) {
                            _result = List<T1>::ctor::Cons_(
                                _f._s0, List<T1>::ctor::Cons_(_f._s1, _result));
                          }},
                      _frame);
                }
                return _result;
              };
              return List<T1>::ctor::Cons_(_args.d_a0, go(_args.d_a1));
            }},
        l->v());
  } /// transpose l transposes a list of lists.

  template <typename T1>
  static std::shared_ptr<List<std::shared_ptr<List<T1>>>>
  transpose_fuel(const unsigned int fuel,
                 std::shared_ptr<List<std::shared_ptr<List<T1>>>> ll) {
    struct _Enter {
      std::shared_ptr<List<std::shared_ptr<List<T1>>>> ll;
      const unsigned int fuel;
    };

    struct _Call1 {
      std::shared_ptr<List<T1>> _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<std::shared_ptr<List<T1>>>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{ll, fuel});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                std::shared_ptr<List<std::shared_ptr<List<T1>>>> ll = _f.ll;
                const unsigned int fuel = _f.fuel;
                if (fuel <= 0) {
                  _result = List<std::shared_ptr<List<T1>>>::ctor::Nil_();
                } else {
                  unsigned int f = fuel - 1;
                  std::function<bool(
                      std::shared_ptr<List<std::shared_ptr<List<T1>>>>)>
                      all_nil;
                  all_nil =
                      [](std::shared_ptr<List<std::shared_ptr<List<T1>>>> l)
                      -> bool {
                    bool _result;
                    std::shared_ptr<List<std::shared_ptr<List<T1>>>> _loop_l =
                        l;
                    bool _continue = true;
                    while (_continue) {
                      std::visit(
                          Overloaded{
                              [&](const typename List<
                                  std::shared_ptr<List<T1>>>::Nil _args) {
                                _result = true;
                                _continue = false;
                              },
                              [&](const typename List<
                                  std::shared_ptr<List<T1>>>::Cons _args) {
                                std::visit(
                                    Overloaded{[&](const typename List<T1>::Nil
                                                       _args0) {
                                                 _loop_l = _args.d_a1;
                                               },
                                               [&](const typename List<T1>::Cons
                                                       _args0) {
                                                 _result = false;
                                                 _continue = false;
                                               }},
                                    _args.d_a0->v());
                              }},
                          _loop_l->v());
                    }
                    return _result;
                  };
                  if (all_nil(ll)) {
                    _result = List<std::shared_ptr<List<T1>>>::ctor::Nil_();
                  } else {
                    std::function<std::shared_ptr<List<T1>>(
                        std::shared_ptr<List<std::shared_ptr<List<T1>>>>)>
                        heads;
                    heads =
                        [&](std::shared_ptr<List<std::shared_ptr<List<T1>>>> l)
                        -> std::shared_ptr<List<T1>> {
                      struct _Enter {
                        std::shared_ptr<List<std::shared_ptr<List<T1>>>> l;
                      };
                      struct _Call1 {
                        decltype(std::declval<const typename List<T1>::Cons &>()
                                     .d_a0) _s0;
                      };
                      using _Frame = std::variant<_Enter, _Call1>;
                      std::shared_ptr<List<T1>> _result{};
                      std::vector<_Frame> _stack;
                      _stack.push_back(_Enter{l});
                      while (!_stack.empty()) {
                        _Frame _frame = std::move(_stack.back());
                        _stack.pop_back();
                        std::visit(
                            Overloaded{
                                [&](_Enter _f) {
                                  std::shared_ptr<
                                      List<std::shared_ptr<List<T1>>>>
                                      l = _f.l;
                                  std::visit(
                                      Overloaded{
                                          [&](const typename List<
                                              std::shared_ptr<List<T1>>>::Nil
                                                  _args0)
                                              -> std::shared_ptr<List<T1>> {
                                            _result = List<T1>::ctor::Nil_();
                                            return {};
                                          },
                                          [&](const typename List<
                                              std::shared_ptr<List<T1>>>::Cons
                                                  _args0)
                                              -> std::shared_ptr<List<T1>> {
                                            std::visit(
                                                Overloaded{
                                                    [&](const typename List<
                                                        T1>::Nil _args1)
                                                        -> std::shared_ptr<
                                                            List<T1>> {
                                                      _stack.push_back(
                                                          _Enter{_args0.d_a1});
                                                      return {};
                                                    },
                                                    [&](const typename List<
                                                        T1>::Cons _args1)
                                                        -> std::shared_ptr<
                                                            List<T1>> {
                                                      _stack.push_back(
                                                          _Call1{_args1.d_a0});
                                                      _stack.push_back(
                                                          _Enter{_args0.d_a1});
                                                      return {};
                                                    }},
                                                _args0.d_a0->v());
                                            return {};
                                          }},
                                      l->v());
                                },
                                [&](_Call1 _f) {
                                  _result =
                                      List<T1>::ctor::Cons_(_f._s0, _result);
                                }},
                            _frame);
                      }
                      return _result;
                    };
                    std::function<
                        std::shared_ptr<List<std::shared_ptr<List<T1>>>>(
                            std::shared_ptr<List<std::shared_ptr<List<T1>>>>)>
                        tails;
                    tails =
                        [&](std::shared_ptr<List<std::shared_ptr<List<T1>>>> l)
                        -> std::shared_ptr<List<std::shared_ptr<List<T1>>>> {
                      struct _Enter {
                        std::shared_ptr<List<std::shared_ptr<List<T1>>>> l;
                      };
                      struct _Call1 {
                        decltype(std::declval<const typename List<T1>::Cons &>()
                                     .d_a1) _s0;
                      };
                      using _Frame = std::variant<_Enter, _Call1>;
                      std::shared_ptr<List<std::shared_ptr<List<T1>>>>
                          _result{};
                      std::vector<_Frame> _stack;
                      _stack.push_back(_Enter{l});
                      while (!_stack.empty()) {
                        _Frame _frame = std::move(_stack.back());
                        _stack.pop_back();
                        std::visit(
                            Overloaded{
                                [&](_Enter _f) {
                                  std::shared_ptr<
                                      List<std::shared_ptr<List<T1>>>>
                                      l = _f.l;
                                  std::visit(
                                      Overloaded{
                                          [&](const typename List<
                                              std::shared_ptr<List<T1>>>::Nil
                                                  _args1)
                                              -> std::shared_ptr<List<
                                                  std::shared_ptr<List<T1>>>> {
                                            _result = List<std::shared_ptr<
                                                List<T1>>>::ctor::Nil_();
                                            return {};
                                          },
                                          [&](const typename List<
                                              std::shared_ptr<List<T1>>>::Cons
                                                  _args1)
                                              -> std::shared_ptr<List<
                                                  std::shared_ptr<List<T1>>>> {
                                            std::visit(
                                                Overloaded{
                                                    [&](const typename List<
                                                        T1>::Nil _args2)
                                                        -> std::shared_ptr<List<
                                                            std::shared_ptr<
                                                                List<T1>>>> {
                                                      _stack.push_back(
                                                          _Enter{_args1.d_a1});
                                                      return {};
                                                    },
                                                    [&](const typename List<
                                                        T1>::Cons _args2)
                                                        -> std::shared_ptr<List<
                                                            std::shared_ptr<
                                                                List<T1>>>> {
                                                      _stack.push_back(
                                                          _Call1{_args2.d_a1});
                                                      _stack.push_back(
                                                          _Enter{_args1.d_a1});
                                                      return {};
                                                    }},
                                                _args1.d_a0->v());
                                            return {};
                                          }},
                                      l->v());
                                },
                                [&](_Call1 _f) {
                                  _result = List<std::shared_ptr<List<T1>>>::
                                      ctor::Cons_(_f._s0, _result);
                                }},
                            _frame);
                      }
                      return _result;
                    };
                    _stack.push_back(_Call1{heads(ll)});
                    _stack.push_back(_Enter{tails(ll), std::move(f)});
                  }
                }
              },
              [&](_Call1 _f) {
                _result = List<std::shared_ptr<List<T1>>>::ctor::Cons_(_f._s0,
                                                                       _result);
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1>
  static std::shared_ptr<List<std::shared_ptr<List<T1>>>>
  transpose(const std::shared_ptr<List<std::shared_ptr<List<T1>>>> &ll) {
    return transpose_fuel<T1>(100u, ll);
  }

  /// collatz_list n generates collatz sequence.
  static std::shared_ptr<List<unsigned int>>
  collatz_list_fuel(const unsigned int fuel, const unsigned int n);
  static std::shared_ptr<List<unsigned int>> collatz_list(const unsigned int n);
  /// run_sum l running sum (scanl for addition).
  static std::shared_ptr<List<unsigned int>>
  run_sum_aux(const unsigned int acc,
              const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  run_sum(std::shared_ptr<List<unsigned int>> l);
  /// rotate_left n l rotates list left by n positions.
  static std::shared_ptr<List<unsigned int>>
  rotate_left_fuel(const unsigned int fuel, const unsigned int n,
                   std::shared_ptr<List<unsigned int>> l);
  static std::shared_ptr<List<unsigned int>>
  rotate_left(const unsigned int n,
              const std::shared_ptr<List<unsigned int>> &l);

  /// iterate f n x generates x, f x, f (f x), ... of length n.
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

  /// sum_acc acc l sum with accumulator.
  __attribute__((pure)) static unsigned int
  sum_acc(const unsigned int acc, const std::shared_ptr<List<unsigned int>> &l);
  /// repeat_string s n repeats string n times (using list as string).
  static std::shared_ptr<List<unsigned int>>
  repeat_string(const std::shared_ptr<List<unsigned int>> &s,
                const unsigned int n);
  /// repeat_with_sep s sep n repeats with separator.
  static std::shared_ptr<List<unsigned int>>
  repeat_with_sep(std::shared_ptr<List<unsigned int>> s,
                  const std::shared_ptr<List<unsigned int>> &sep,
                  const unsigned int n);
  /// string_chain s n recursive string chain: s-chain(s, n-1)-end.
  static std::shared_ptr<List<unsigned int>> string_chain_fuel(
      const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &s,
      const unsigned int n, const std::shared_ptr<List<unsigned int>> &sep,
      const std::shared_ptr<List<unsigned int>> &end_marker);
  static std::shared_ptr<List<unsigned int>>
  string_chain(const std::shared_ptr<List<unsigned int>> &s,
               const unsigned int n,
               const std::shared_ptr<List<unsigned int>> &sep,
               const std::shared_ptr<List<unsigned int>> &end_marker);
  /// split_by_sign l base pos neg splits list based on base threshold.
  __attribute__((pure)) static std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
  split_by_sign(const std::shared_ptr<List<unsigned int>> &l,
                const unsigned int base,
                std::shared_ptr<List<unsigned int>> pos,
                std::shared_ptr<List<unsigned int>> neg);
  /// differences l computes differences between consecutive elements.
  static std::shared_ptr<List<unsigned int>>
  differences(const std::shared_ptr<List<unsigned int>> &l);
  /// replace_at idx value l replaces element at index with value.
  static std::shared_ptr<List<unsigned int>>
  replace_at(const unsigned int idx, const unsigned int value,
             const std::shared_ptr<List<unsigned int>> &l);
  /// cycle n l repeats list n times.
  static std::shared_ptr<List<unsigned int>>
  cycle(const unsigned int n, const std::shared_ptr<List<unsigned int>> &l);
  /// Helper: get first element.
  __attribute__((pure)) static unsigned int
  first_elem(const std::shared_ptr<List<unsigned int>> &l);
  /// Helper: get last element.
  __attribute__((pure)) static unsigned int
  last_elem(const std::shared_ptr<List<unsigned int>> &l);
  /// Helper: remove first element.
  static std::shared_ptr<List<unsigned int>>
  tail_list(const std::shared_ptr<List<unsigned int>> &l);
  /// Helper: remove last element.
  static std::shared_ptr<List<unsigned int>>
  init_list(const std::shared_ptr<List<unsigned int>> &l);
  /// is_palindrome s checks if list is a palindrome.
  __attribute__((pure)) static bool
  is_palindrome_fuel(const unsigned int fuel,
                     const std::shared_ptr<List<unsigned int>> &s);
  __attribute__((pure)) static bool
  is_palindrome(const std::shared_ptr<List<unsigned int>> &s);
  /// string_subsequences s generates all subsequences treating list as string.
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  string_subsequences(const std::shared_ptr<List<unsigned int>> &s);
  /// run_length_groups l groups consecutive runs into sublist lengths.
  static std::shared_ptr<List<unsigned int>>
  run_length_groups_aux(const unsigned int prev, const unsigned int count,
                        const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  run_length_groups(const std::shared_ptr<List<unsigned int>> &l);
  /// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
  __attribute__((pure)) static bool
  is_prefix_of(const std::shared_ptr<List<unsigned int>> &l1,
               const std::shared_ptr<List<unsigned int>> &l2);
  /// lis l longest increasing subsequence (greedy, not optimal).
  static std::shared_ptr<List<unsigned int>>
  lis(std::shared_ptr<List<unsigned int>> l);

  /// take_while p l takes elements while predicate holds.
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

  /// drop_while p l drops elements while predicate holds.
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  drop_while(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    std::shared_ptr<List<unsigned int>> _result;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                              _result = List<unsigned int>::ctor::Nil_();
                              _continue = false;
                            },
                            [&](const typename List<unsigned int>::Cons _args) {
                              if (p(_args.d_a0)) {
                                _loop_l = _args.d_a1;
                              } else {
                                _result = List<unsigned int>::ctor::Cons_(
                                    _args.d_a0, _args.d_a1);
                                _continue = false;
                              }
                            }},
                 _loop_l->v());
    }
    return _result;
  }

  /// Helper: check if element is in list.
  __attribute__((pure)) static bool
  elem(const unsigned int x, const std::shared_ptr<List<unsigned int>> &l);
  /// Helper: filter list.
  static std::shared_ptr<List<unsigned int>>
  filter_ne(const unsigned int x, const std::shared_ptr<List<unsigned int>> &l);
  /// nub l removes duplicates from list.
  static std::shared_ptr<List<unsigned int>>
  nub_fuel(const unsigned int fuel,
           const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  nub(const std::shared_ptr<List<unsigned int>> &l);
  /// group l groups consecutive equal elements.
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  group_fuel(const unsigned int fuel,
             const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  group(const std::shared_ptr<List<unsigned int>> &l);
  /// Helper: get head with default.
  __attribute__((pure)) static unsigned int
  head_or(const unsigned int default0,
          const std::shared_ptr<List<unsigned int>> &l);
  /// remove_if_sum_even l removes elements where sum with next is even.
  static std::shared_ptr<List<unsigned int>>
  remove_if_sum_even(const std::shared_ptr<List<unsigned int>> &l);

  /// bool_all p l checks if all elements satisfy predicate (forall with &&).
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool
  bool_all(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
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

  /// run_length_encode l encodes consecutive runs: 1,1,2,2,2 -> (1,2),(2,3).
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  run_length_encode_fuel(const unsigned int fuel,
                         const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
  run_length_encode(const std::shared_ptr<List<unsigned int>> &l);
  /// between lo hi l filters elements in range lo, hi.
  static std::shared_ptr<List<unsigned int>>
  between(const unsigned int lo, const unsigned int hi,
          const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_SEQUENCES
