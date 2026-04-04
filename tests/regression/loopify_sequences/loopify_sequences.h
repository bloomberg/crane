#ifndef INCLUDED_LOOPIFY_SEQUENCES
#define INCLUDED_LOOPIFY_SEQUENCES

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
                                _args) -> void { _result = List<T1>::nil(); },
                        [&](const typename List<std::shared_ptr<List<T1>>>::Cons
                                _args) -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<
                                      std::shared_ptr<List<T1>>>::Nil _args0)
                                      -> void { _result = _args.d_a0; },
                                  [&](const typename List<
                                      std::shared_ptr<List<T1>>>::Cons _args0)
                                      -> void {
                                    _stack.push_back(_Call1{_args.d_a0, sep});
                                    _stack.push_back(_Enter{_args.d_a1});
                                  }},
                              _args.d_a1->v());
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
                -> std::shared_ptr<List<T1>> { return List<T1>::nil(); },
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
                                        -> void { _result = List<T1>::nil(); },
                                    [&](const typename List<T1>::Cons _args0)
                                        -> void {
                                      _stack.push_back(
                                          _Call1{sep, _args0.d_a0});
                                      _stack.push_back(_Enter{_args0.d_a1});
                                    }},
                                rest->v());
                          },
                          [&](_Call1 _f) {
                            _result = List<T1>::cons(
                                _f._s0, List<T1>::cons(_f._s1, _result));
                          }},
                      _frame);
                }
                return _result;
              };
              return List<T1>::cons(_args.d_a0, go(_args.d_a1));
            }},
        l->v());
  } /// transpose l transposes a list of lists.

  template <typename T1>
  static std::shared_ptr<List<std::shared_ptr<List<T1>>>>
  transpose_fuel(const unsigned int fuel,
                 std::shared_ptr<List<std::shared_ptr<List<T1>>>> ll) {
    std::shared_ptr<List<std::shared_ptr<List<T1>>>> _head{};
    std::shared_ptr<List<std::shared_ptr<List<T1>>>> _last{};
    std::shared_ptr<List<std::shared_ptr<List<T1>>>> _loop_ll = ll;
    unsigned int _loop_fuel = fuel;
    bool _continue = true;
    while (_continue) {
      if (_loop_fuel <= 0) {
        {
          if (_last) {
            std::get<typename List<std::shared_ptr<List<T1>>>::Cons>(
                _last->v_mut())
                .d_a1 = List<std::shared_ptr<List<T1>>>::nil();
          } else {
            _head = List<std::shared_ptr<List<T1>>>::nil();
          }
          _continue = false;
        }
      } else {
        unsigned int f = _loop_fuel - 1;
        std::function<bool(std::shared_ptr<List<std::shared_ptr<List<T1>>>>)>
            all_nil;
        all_nil =
            [](std::shared_ptr<List<std::shared_ptr<List<T1>>>> l) -> bool {
          bool _result;
          std::shared_ptr<List<std::shared_ptr<List<T1>>>> _loop_l = l;
          bool _continue = true;
          while (_continue) {
            std::visit(
                Overloaded{
                    [&](const typename List<std::shared_ptr<List<T1>>>::Nil
                            _args) {
                      _result = true;
                      _continue = false;
                    },
                    [&](const typename List<std::shared_ptr<List<T1>>>::Cons
                            _args) {
                      std::visit(
                          Overloaded{[&](const typename List<T1>::Nil _args0) {
                                       _loop_l = _args.d_a1;
                                     },
                                     [&](const typename List<T1>::Cons _args0) {
                                       _result = false;
                                       _continue = false;
                                     }},
                          _args.d_a0->v());
                    }},
                _loop_l->v());
          }
          return _result;
        };
        if (all_nil(_loop_ll)) {
          {
            if (_last) {
              std::get<typename List<std::shared_ptr<List<T1>>>::Cons>(
                  _last->v_mut())
                  .d_a1 = List<std::shared_ptr<List<T1>>>::nil();
            } else {
              _head = List<std::shared_ptr<List<T1>>>::nil();
            }
            _continue = false;
          }
        } else {
          std::function<std::shared_ptr<List<T1>>(
              std::shared_ptr<List<std::shared_ptr<List<T1>>>>)>
              heads;
          heads = [&](std::shared_ptr<List<std::shared_ptr<List<T1>>>> l)
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
                        std::shared_ptr<List<std::shared_ptr<List<T1>>>> l =
                            _f.l;
                        std::visit(
                            Overloaded{
                                [&](const typename List<
                                    std::shared_ptr<List<T1>>>::Nil _args0)
                                    -> void { _result = List<T1>::nil(); },
                                [&](const typename List<
                                    std::shared_ptr<List<T1>>>::Cons _args0)
                                    -> void {
                                  std::visit(
                                      Overloaded{
                                          [&](const typename List<T1>::Nil
                                                  _args1) -> void {
                                            _stack.push_back(
                                                _Enter{_args0.d_a1});
                                          },
                                          [&](const typename List<T1>::Cons
                                                  _args1) -> void {
                                            _stack.push_back(
                                                _Call1{_args1.d_a0});
                                            _stack.push_back(
                                                _Enter{_args0.d_a1});
                                          }},
                                      _args0.d_a0->v());
                                }},
                            l->v());
                      },
                      [&](_Call1 _f) {
                        _result = List<T1>::cons(_f._s0, _result);
                      }},
                  _frame);
            }
            return _result;
          };
          std::function<std::shared_ptr<List<std::shared_ptr<List<T1>>>>(
              std::shared_ptr<List<std::shared_ptr<List<T1>>>>)>
              tails;
          tails = [&](std::shared_ptr<List<std::shared_ptr<List<T1>>>> l)
              -> std::shared_ptr<List<std::shared_ptr<List<T1>>>> {
            struct _Enter {
              std::shared_ptr<List<std::shared_ptr<List<T1>>>> l;
            };
            struct _Call1 {
              decltype(std::declval<const typename List<T1>::Cons &>()
                           .d_a1) _s0;
            };
            using _Frame = std::variant<_Enter, _Call1>;
            std::shared_ptr<List<std::shared_ptr<List<T1>>>> _result{};
            std::vector<_Frame> _stack;
            _stack.push_back(_Enter{l});
            while (!_stack.empty()) {
              _Frame _frame = std::move(_stack.back());
              _stack.pop_back();
              std::visit(
                  Overloaded{
                      [&](_Enter _f) {
                        std::shared_ptr<List<std::shared_ptr<List<T1>>>> l =
                            _f.l;
                        std::visit(
                            Overloaded{
                                [&](const typename List<
                                    std::shared_ptr<List<T1>>>::Nil _args1)
                                    -> void {
                                  _result =
                                      List<std::shared_ptr<List<T1>>>::nil();
                                },
                                [&](const typename List<
                                    std::shared_ptr<List<T1>>>::Cons _args1)
                                    -> void {
                                  std::visit(
                                      Overloaded{
                                          [&](const typename List<T1>::Nil
                                                  _args2) -> void {
                                            _stack.push_back(
                                                _Enter{_args1.d_a1});
                                          },
                                          [&](const typename List<T1>::Cons
                                                  _args2) -> void {
                                            _stack.push_back(
                                                _Call1{_args2.d_a1});
                                            _stack.push_back(
                                                _Enter{_args1.d_a1});
                                          }},
                                      _args1.d_a0->v());
                                }},
                            l->v());
                      },
                      [&](_Call1 _f) {
                        _result = List<std::shared_ptr<List<T1>>>::cons(
                            _f._s0, _result);
                      }},
                  _frame);
            }
            return _result;
          };
          {
            auto _cell =
                List<std::shared_ptr<List<T1>>>::cons(heads(_loop_ll), nullptr);
            if (_last) {
              std::get<typename List<std::shared_ptr<List<T1>>>::Cons>(
                  _last->v_mut())
                  .d_a1 = _cell;
            } else {
              _head = _cell;
            }
            _last = _cell;
            std::shared_ptr<List<std::shared_ptr<List<T1>>>> _next_ll =
                tails(_loop_ll);
            unsigned int _next_fuel = f;
            _loop_ll = std::move(_next_ll);
            _loop_fuel = std::move(_next_fuel);
            continue;
          }
        }
      }
    }
    return _head;
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
          unsigned int _next_n = m;
          _loop_x = std::move(_next_x);
          _loop_n = std::move(_next_n);
          continue;
        }
      }
    }
    return _head;
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

  /// drop_while p l drops elements while predicate holds.
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  drop_while(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    std::shared_ptr<List<unsigned int>> _result;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                              _result = List<unsigned int>::nil();
                              _continue = false;
                            },
                            [&](const typename List<unsigned int>::Cons _args) {
                              if (p(_args.d_a0)) {
                                _loop_l = _args.d_a1;
                              } else {
                                _result = List<unsigned int>::cons(_args.d_a0,
                                                                   _args.d_a1);
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
