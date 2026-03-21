#ifndef INCLUDED_LOOPIFY_PATTERNS
#define INCLUDED_LOOPIFY_PATTERNS

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

struct Nat {
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int x, const unsigned int y, const unsigned int q,
         const unsigned int u);
  __attribute__((pure)) static unsigned int div(const unsigned int x,
                                                const unsigned int y);
};

/// Complex control flow and pattern matching edge cases.
struct LoopifyPatterns {
  template <typename t_A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      t_A d_a0;
      std::shared_ptr<list<t_A>> d_a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit list(Nil _v) : d_v_(std::move(_v)) {}

    explicit list(Cons _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<list<t_A>> Nil_() {
        return std::shared_ptr<list<t_A>>(new list<t_A>(Nil{}));
      }

      static std::shared_ptr<list<t_A>>
      Cons_(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
        return std::shared_ptr<list<t_A>>(new list<t_A>(Cons{a0, a1}));
      }

      static std::unique_ptr<list<t_A>> Nil_uptr() {
        return std::unique_ptr<list<t_A>>(new list<t_A>(Nil{}));
      }

      static std::unique_ptr<list<t_A>>
      Cons_uptr(t_A a0, const std::shared_ptr<list<t_A>> &a1) {
        return std::unique_ptr<list<t_A>>(new list<t_A>(Cons{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename list<T1>::Cons &>().d_a1) _s0;
      decltype(std::declval<const typename list<T1>::Cons &>().d_a0) _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
                       const std::shared_ptr<list<T1>> l = _f.l;
                       std::visit(
                           Overloaded{
                               [&](const typename list<T1>::Nil _args) -> T2 {
                                 _result = f;
                                 return {};
                               },
                               [&](const typename list<T1>::Cons _args) -> T2 {
                                 _stack.push_back(
                                     _Call1{_args.d_a1, _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a1});
                                 return {};
                               }},
                           l->v());
                     },
                     [&](_Call1 _f) { _result = f0(_f._s1, _f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  template <typename T1, typename T2,
            MapsTo<T2, T1, std::shared_ptr<list<T1>>, T2> F1>
  static T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename list<T1>::Cons &>().d_a1) _s0;
      decltype(std::declval<const typename list<T1>::Cons &>().d_a0) _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    T2 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
                       const std::shared_ptr<list<T1>> l = _f.l;
                       std::visit(
                           Overloaded{
                               [&](const typename list<T1>::Nil _args) -> T2 {
                                 _result = f;
                                 return {};
                               },
                               [&](const typename list<T1>::Cons _args) -> T2 {
                                 _stack.push_back(
                                     _Call1{_args.d_a1, _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a1});
                                 return {};
                               }},
                           l->v());
                     },
                     [&](_Call1 _f) { _result = f0(_f._s1, _f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  /// multi_let n multiple sequential let bindings before recursion.
  __attribute__((pure)) static unsigned int multi_let(const unsigned int n);
  /// nested_if n deeply nested if-then-else with recursion at different depths.
  __attribute__((pure)) static unsigned int
  nested_if_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int nested_if(const unsigned int n);
  /// deep_nest n deeply nested function application.
  __attribute__((pure)) static unsigned int deep_nest(const unsigned int n);
  /// bool_chain n target multiple recursive calls in || chain.
  __attribute__((pure)) static bool bool_chain_fuel(const unsigned int fuel,
                                                    const unsigned int n,
                                                    const unsigned int target);
  __attribute__((pure)) static bool bool_chain(const unsigned int n,
                                               const unsigned int target);
  /// chained_comp n boolean result with double recursion.
  __attribute__((pure)) static bool chained_comp(const unsigned int n);
  /// tuple_constr n recursive calls in multiple tuple positions.
  __attribute__((pure)) static std::pair<std::pair<unsigned int, unsigned int>,
                                         unsigned int>
  tuple_constr(const unsigned int n);
  /// sum_prod_count l a_sum a_prod a_count multiple accumulator updates.
  __attribute__((pure)) static std::pair<std::pair<unsigned int, unsigned int>,
                                         unsigned int>
  sum_prod_count(const std::shared_ptr<list<unsigned int>> &l,
                 const unsigned int a_sum, const unsigned int a_prod,
                 const unsigned int a_count);
  /// split_by_sign l pos neg partition with dual accumulators.
  __attribute__((pure)) static std::pair<std::shared_ptr<list<unsigned int>>,
                                         std::shared_ptr<list<unsigned int>>>
  split_by_sign_aux(const std::shared_ptr<list<unsigned int>> &l,
                    const unsigned int base,
                    std::shared_ptr<list<unsigned int>> pos,
                    std::shared_ptr<list<unsigned int>> neg);
  __attribute__((pure)) static std::pair<std::shared_ptr<list<unsigned int>>,
                                         std::shared_ptr<list<unsigned int>>>
  split_by_sign(const std::shared_ptr<list<unsigned int>> &l,
                const unsigned int base);
  /// guard_accum acc l multiple when-style guards with different logic.
  __attribute__((pure)) static unsigned int
  guard_accum(const unsigned int acc,
              const std::shared_ptr<list<unsigned int>> &l);
  /// cons_computed n l cons with conditional parameter change.
  static std::shared_ptr<list<unsigned int>>
  cons_computed(const unsigned int n,
                const std::shared_ptr<list<unsigned int>> &l);
  /// mod_pattern n recursive call in mod expression.
  __attribute__((pure)) static unsigned int mod_pattern(const unsigned int n);
  /// alternating_ops n alternating operations based on modulo.
  __attribute__((pure)) static unsigned int
  alternating_ops(const unsigned int n);

  /// max_by f l recursive max with function application.
  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  max_by(F0 &&f, const std::shared_ptr<list<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<list<unsigned int>> l;
    };

    struct _Call1 {
      const typename list<unsigned int>::Cons _s0;
      F0 _s1;
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
                const std::shared_ptr<list<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list<unsigned int>::Nil _args)
                            -> unsigned int {
                          _result = 0u;
                          return {};
                        },
                        [&](const typename list<unsigned int>::Cons _args)
                            -> unsigned int {
                          std::visit(
                              Overloaded{
                                  [&](const typename list<unsigned int>::Nil
                                          _args0) -> unsigned int {
                                    _result = f(_args.d_a0);
                                    return {};
                                  },
                                  [&](const typename list<unsigned int>::Cons
                                          _args0) -> unsigned int {
                                    _stack.push_back(_Call1{_args, f});
                                    _stack.push_back(_Enter{_args.d_a1});
                                    return {};
                                  }},
                              _args.d_a1->v());
                          return {};
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename list<unsigned int>::Cons _args = _f._s0;
                F0 f = _f._s1;
                unsigned int rest_max = _result;
                unsigned int fx = f(_args.d_a0);
                if (fx < rest_max) {
                  _result = std::move(rest_max);
                } else {
                  _result = std::move(fx);
                }
              }},
          _frame);
    }
    return _result;
  }

  /// replace_at idx value l replace element at index.
  static std::shared_ptr<list<unsigned int>>
  replace_at(const unsigned int idx, const unsigned int value,
             const std::shared_ptr<list<unsigned int>> &l);
  /// nested_pattern l three-element tuple pattern.
  __attribute__((pure)) static unsigned int nested_pattern(
      const std::shared_ptr<
          list<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
          &l);
  /// let_nested n let with nested let in binding.
  __attribute__((pure)) static unsigned int let_nested(const unsigned int n);

  /// insert_everywhere x l insert element at all possible positions.
  template <typename T1>
  static std::shared_ptr<list<std::shared_ptr<list<T1>>>>
  insert_everywhere(const T1 x, const std::shared_ptr<list<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<list<T1>> l;
    };

    struct _Call1 {
      decltype(list<T1>::ctor::Cons_(
          std::declval<const T1 &>(),
          list<T1>::ctor::Cons_(
              std::declval<const typename list<T1>::Cons &>().d_a0,
              std::declval<const typename list<T1>::Cons &>().d_a1))) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<list<std::shared_ptr<list<T1>>>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<list<T1>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list<T1>::Nil _args)
                            -> std::shared_ptr<
                                list<std::shared_ptr<list<T1>>>> {
                          _result =
                              list<std::shared_ptr<list<T1>>>::ctor::Cons_(
                                  list<T1>::ctor::Cons_(x,
                                                        list<T1>::ctor::Nil_()),
                                  list<
                                      std::shared_ptr<list<T1>>>::ctor::Nil_());
                          return {};
                        },
                        [&](const typename list<T1>::Cons _args)
                            -> std::shared_ptr<
                                list<std::shared_ptr<list<T1>>>> {
                          std::function<std::shared_ptr<
                              list<std::shared_ptr<list<T1>>>>(
                              std::shared_ptr<list<std::shared_ptr<list<T1>>>>)>
                              map_cons_h;
                          map_cons_h = [&](std::shared_ptr<
                                           list<std::shared_ptr<list<T1>>>>
                                               lsts)
                              -> std::shared_ptr<
                                  list<std::shared_ptr<list<T1>>>> {
                            struct _Enter {
                              std::shared_ptr<list<std::shared_ptr<list<T1>>>>
                                  lsts;
                            };
                            struct _Call1 {
                              decltype(list<T1>::ctor::Cons_(
                                  _args.d_a0,
                                  std::declval<const typename list<
                                      std::shared_ptr<list<T1>>>::Cons &>()
                                      .d_a0)) _s0;
                            };
                            using _Frame = std::variant<_Enter, _Call1>;
                            std::shared_ptr<list<std::shared_ptr<list<T1>>>>
                                _result{};
                            std::vector<_Frame> _stack;
                            _stack.push_back(_Enter{lsts});
                            while (!_stack.empty()) {
                              _Frame _frame = std::move(_stack.back());
                              _stack.pop_back();
                              std::visit(
                                  Overloaded{
                                      [&](_Enter _f) {
                                        std::shared_ptr<
                                            list<std::shared_ptr<list<T1>>>>
                                            lsts = _f.lsts;
                                        std::visit(
                                            Overloaded{
                                                [&](const typename list<
                                                    std::shared_ptr<list<T1>>>::
                                                        Nil _args0)
                                                    -> std::shared_ptr<
                                                        list<std::shared_ptr<
                                                            list<T1>>>> {
                                                  _result =
                                                      list<std::shared_ptr<list<
                                                          T1>>>::ctor::Nil_();
                                                  return {};
                                                },
                                                [&](const typename list<
                                                    std::shared_ptr<list<T1>>>::
                                                        Cons _args0)
                                                    -> std::shared_ptr<
                                                        list<std::shared_ptr<
                                                            list<T1>>>> {
                                                  _stack.push_back(_Call1{
                                                      list<T1>::ctor::Cons_(
                                                          _args.d_a0,
                                                          _args0.d_a0)});
                                                  _stack.push_back(
                                                      _Enter{_args0.d_a1});
                                                  return {};
                                                }},
                                            lsts->v());
                                      },
                                      [&](_Call1 _f) {
                                        _result =
                                            list<std::shared_ptr<list<T1>>>::
                                                ctor::Cons_(_f._s0, _result);
                                      }},
                                  _frame);
                            }
                            return _result;
                          };
                          _stack.push_back(_Call1{list<T1>::ctor::Cons_(
                              x,
                              list<T1>::ctor::Cons_(_args.d_a0, _args.d_a1))});
                          _stack.push_back(_Enter{_args.d_a1});
                          return {};
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                _result = list<std::shared_ptr<list<T1>>>::ctor::Cons_(
                    _f._s0, map_cons_h(_result));
              }},
          _frame);
    }
    return _result;
  }

  /// Helper: list length.
  __attribute__((pure)) static unsigned int
  list_len(const std::shared_ptr<list<unsigned int>> &l);

  /// merge_by cmp l1 l2 merge with custom comparator.
  template <MapsTo<unsigned int, unsigned int, unsigned int> F1>
  static std::shared_ptr<list<unsigned int>>
  merge_by_fuel(const unsigned int fuel, F1 &&cmp,
                std::shared_ptr<list<unsigned int>> l1,
                std::shared_ptr<list<unsigned int>> l2) {
    struct _Enter {
      std::shared_ptr<list<unsigned int>> l2;
      std::shared_ptr<list<unsigned int>> l1;
      const unsigned int fuel;
    };

    struct _Call1 {
      decltype(std::declval<const typename list<unsigned int>::Cons &>()
                   .d_a0) _s0;
    };

    struct _Call2 {
      decltype(std::declval<const typename list<unsigned int>::Cons &>()
                   .d_a0) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    std::shared_ptr<list<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l2, l1, fuel});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                std::shared_ptr<list<unsigned int>> l2 = _f.l2;
                std::shared_ptr<list<unsigned int>> l1 = _f.l1;
                const unsigned int fuel = _f.fuel;
                if (fuel <= 0) {
                  _result = std::move(l1);
                } else {
                  unsigned int f = fuel - 1;
                  std::visit(
                      Overloaded{
                          [&](const typename list<unsigned int>::Nil _args)
                              -> std::shared_ptr<list<unsigned int>> {
                            _result = std::move(l2);
                            return {};
                          },
                          [&](const typename list<unsigned int>::Cons _args)
                              -> std::shared_ptr<list<unsigned int>> {
                            std::visit(
                                Overloaded{
                                    [&](const typename list<unsigned int>::Nil
                                            _args0)
                                        -> std::shared_ptr<list<unsigned int>> {
                                      _result = l1;
                                      return {};
                                    },
                                    [&](const typename list<unsigned int>::Cons
                                            _args0)
                                        -> std::shared_ptr<list<unsigned int>> {
                                      if (cmp(_args.d_a0, _args0.d_a0) <= 0u) {
                                        _stack.push_back(_Call1{_args.d_a0});
                                        _stack.push_back(_Enter{std::move(l2),
                                                                _args.d_a1,
                                                                std::move(f)});
                                      } else {
                                        _stack.push_back(_Call2{_args0.d_a0});
                                        _stack.push_back(_Enter{_args0.d_a1, l1,
                                                                std::move(f)});
                                      }
                                      return {};
                                    }},
                                l2->v());
                            return {};
                          }},
                      l1->v());
                }
              },
              [&](_Call1 _f) {
                _result = list<unsigned int>::ctor::Cons_(_f._s0, _result);
              },
              [&](_Call2 _f) {
                _result = list<unsigned int>::ctor::Cons_(_f._s0, _result);
              }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  static std::shared_ptr<list<unsigned int>>
  merge_by(F0 &&cmp, const std::shared_ptr<list<unsigned int>> &l1,
           const std::shared_ptr<list<unsigned int>> &l2) {
    return merge_by_fuel((list_len(l1) + list_len(l2)), cmp, l1, l2);
  }

  /// process_twice l applies recursion twice: process(process(xs)).
  static std::shared_ptr<list<unsigned int>>
  process_twice_fuel(const unsigned int fuel,
                     std::shared_ptr<list<unsigned int>> l);
  static std::shared_ptr<list<unsigned int>>
  process_twice(const std::shared_ptr<list<unsigned int>> &l);
  /// as_guard l uses as-pattern with guard (length check).
  static std::shared_ptr<list<unsigned int>>
  as_guard_fuel(const unsigned int fuel,
                const std::shared_ptr<list<unsigned int>> &l);
  static std::shared_ptr<list<unsigned int>>
  as_guard(const std::shared_ptr<list<unsigned int>> &l);
  /// quad_sum_pattern l pattern with 4-way split.
  __attribute__((pure)) static unsigned int
  quad_sum_pattern(const std::shared_ptr<list<unsigned int>> &l);
  /// multi_guard l demonstrates pattern with multiple conditional branches.
  __attribute__((pure)) static unsigned int
  multi_guard(const std::shared_ptr<list<unsigned int>> &l);
  /// Internal helper for double_append.
  static std::shared_ptr<list<unsigned int>>
  append_lists(const std::shared_ptr<list<unsigned int>> &l1,
               std::shared_ptr<list<unsigned int>> l2);
  /// double_append l1 l2 uses recursive result twice: h :: (rest @ rest).
  static std::shared_ptr<list<unsigned int>>
  double_append(const std::shared_ptr<list<unsigned int>> &l1,
                std::shared_ptr<list<unsigned int>> l2);
  /// process_twice_alt l applies transformation twice on recursive result.
  static std::shared_ptr<list<unsigned int>>
  process_twice_alt_fuel(const unsigned int fuel,
                         std::shared_ptr<list<unsigned int>> l);
  static std::shared_ptr<list<unsigned int>>
  process_twice_alt(const std::shared_ptr<list<unsigned int>> &l);
  /// sum_if_positive_else_double l conditional logic on each element.
  __attribute__((pure)) static unsigned int
  sum_if_positive_else_double(const std::shared_ptr<list<unsigned int>> &l);

  /// take_until p l takes elements until predicate is true.
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<list<unsigned int>>
  take_until(F0 &&p, const std::shared_ptr<list<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<list<unsigned int>> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename list<unsigned int>::Cons &>()
                   .d_a0) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<list<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<list<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list<unsigned int>::Nil _args)
                            -> std::shared_ptr<list<unsigned int>> {
                          _result = list<unsigned int>::ctor::Nil_();
                          return {};
                        },
                        [&](const typename list<unsigned int>::Cons _args)
                            -> std::shared_ptr<list<unsigned int>> {
                          if (p(_args.d_a0)) {
                            _result = list<unsigned int>::ctor::Nil_();
                          } else {
                            _stack.push_back(_Call1{_args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1});
                          }
                          return {};
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                _result = list<unsigned int>::ctor::Cons_(_f._s0, _result);
              }},
          _frame);
    }
    return _result;
  }

  /// partition_by p q l partitions into 3 categories based on two predicates.
  template <MapsTo<bool, unsigned int> F0, MapsTo<bool, unsigned int> F1>
  __attribute__((
      pure)) static std::pair<std::pair<std::shared_ptr<list<unsigned int>>,
                                        std::shared_ptr<list<unsigned int>>>,
                              std::shared_ptr<list<unsigned int>>>
  partition_by(F0 &&p, F1 &&q, const std::shared_ptr<list<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<list<unsigned int>> l;
    };

    struct _Call1 {
      F0 _s0;
      const typename list<unsigned int>::Cons _s1;
      F1 _s2;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::pair<std::shared_ptr<list<unsigned int>>,
                        std::shared_ptr<list<unsigned int>>>,
              std::shared_ptr<list<unsigned int>>>
        _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<list<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list<unsigned int>::Nil _args)
                            -> std::pair<
                                std::pair<std::shared_ptr<list<unsigned int>>,
                                          std::shared_ptr<list<unsigned int>>>,
                                std::shared_ptr<list<unsigned int>>> {
                          _result = std::make_pair(
                              std::make_pair(list<unsigned int>::ctor::Nil_(),
                                             list<unsigned int>::ctor::Nil_()),
                              list<unsigned int>::ctor::Nil_());
                          return {};
                        },
                        [&](const typename list<unsigned int>::Cons _args)
                            -> std::pair<
                                std::pair<std::shared_ptr<list<unsigned int>>,
                                          std::shared_ptr<list<unsigned int>>>,
                                std::shared_ptr<list<unsigned int>>> {
                          _stack.push_back(_Call1{p, _args, q});
                          _stack.push_back(_Enter{_args.d_a1});
                          return {};
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                F0 p = _f._s0;
                const typename list<unsigned int>::Cons _args = _f._s1;
                F1 q = _f._s2;
                std::pair<std::shared_ptr<list<unsigned int>>,
                          std::shared_ptr<list<unsigned int>>>
                    p0 = _result.first;
                std::shared_ptr<list<unsigned int>> cs = _result.second;
                std::shared_ptr<list<unsigned int>> as_ = p0.first;
                std::shared_ptr<list<unsigned int>> bs = p0.second;
                if (p(_args.d_a0)) {
                  _result = std::make_pair(
                      std::make_pair(
                          list<unsigned int>::ctor::Cons_(_args.d_a0, as_), bs),
                      cs);
                } else {
                  if (q(_args.d_a0)) {
                    _result = std::make_pair(
                        std::make_pair(as_, list<unsigned int>::ctor::Cons_(
                                                _args.d_a0, bs)),
                        cs);
                  } else {
                    _result = std::make_pair(
                        std::make_pair(as_, bs),
                        list<unsigned int>::ctor::Cons_(_args.d_a0, cs));
                  }
                }
              }},
          _frame);
    }
    return _result;
  }

  /// merge_alternating l1 l2 merges two lists by alternating elements.
  static std::shared_ptr<list<unsigned int>>
  merge_alternating(std::shared_ptr<list<unsigned int>> l1,
                    std::shared_ptr<list<unsigned int>> l2);

  /// filter_map_indexed p f l filters and maps with index.
  template <MapsTo<bool, unsigned int, unsigned int> F0,
            MapsTo<unsigned int, unsigned int> F1>
  static std::shared_ptr<list<unsigned int>>
  filter_map_indexed_aux(F0 &&p, F1 &&f,
                         const std::shared_ptr<list<unsigned int>> &l,
                         const unsigned int idx) {
    struct _Enter {
      const unsigned int idx;
      const std::shared_ptr<list<unsigned int>> l;
    };

    struct _Call1 {
      unsigned int _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<list<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{idx, l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const unsigned int idx = _f.idx;
                const std::shared_ptr<list<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list<unsigned int>::Nil _args)
                            -> std::shared_ptr<list<unsigned int>> {
                          _result = list<unsigned int>::ctor::Nil_();
                          return {};
                        },
                        [&](const typename list<unsigned int>::Cons _args)
                            -> std::shared_ptr<list<unsigned int>> {
                          if (p(idx, _args.d_a0)) {
                            _stack.push_back(_Call1{f(_args.d_a0)});
                            _stack.push_back(
                                _Enter{(std::move(idx) + 1), _args.d_a1});
                          } else {
                            _stack.push_back(
                                _Enter{(std::move(idx) + 1), _args.d_a1});
                          }
                          return {};
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                _result = list<unsigned int>::ctor::Cons_(_f._s0, _result);
              }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int, unsigned int> F0,
            MapsTo<unsigned int, unsigned int> F1>
  static std::shared_ptr<list<unsigned int>>
  filter_map_indexed(F0 &&p, F1 &&f,
                     const std::shared_ptr<list<unsigned int>> &l) {
    return filter_map_indexed_aux(p, f, l, 0u);
  }

  /// four_elem l four-element destructuring pattern with fallback cases.
  __attribute__((pure)) static unsigned int
  four_elem(const std::shared_ptr<list<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_PATTERNS
