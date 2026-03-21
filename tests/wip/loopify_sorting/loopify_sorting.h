#ifndef INCLUDED_LOOPIFY_SORTING
#define INCLUDED_LOOPIFY_SORTING

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

/// Consolidated UNIQUE sorting algorithms and related operations.
struct LoopifySorting {
  template <typename T1>
  __attribute__((pure)) static unsigned int
  len_impl(const std::shared_ptr<List<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<List<T1>> l;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
                       const std::shared_ptr<List<T1>> l = _f.l;
                       std::visit(
                           Overloaded{[&](const typename List<T1>::Nil _args)
                                          -> unsigned int {
                                        _result = 0u;
                                        return {};
                                      },
                                      [&](const typename List<T1>::Cons _args)
                                          -> unsigned int {
                                        _stack.push_back(_Call1{});
                                        _stack.push_back(_Enter{_args.d_a1});
                                        return {};
                                      }},
                           l->v());
                     },
                     [&](_Call1 _f) { _result = (_result + 1); }},
          _frame);
    }
    return _result;
  }

  static std::shared_ptr<List<unsigned int>>
  insert(const unsigned int x, std::shared_ptr<List<unsigned int>> l);
  static std::shared_ptr<List<unsigned int>>
  insertion_sort(const std::shared_ptr<List<unsigned int>> &l);

  template <typename T1>
  __attribute__((pure)) static std::pair<std::shared_ptr<List<T1>>,
                                         std::shared_ptr<List<T1>>>
  split(const std::shared_ptr<List<T1>> &l) {
    struct _Enter {
      const std::shared_ptr<List<T1>> l;
    };

    struct _Call1 {
      const typename List<T1>::Cons _s0;
      const typename List<T1>::Cons _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::pair<std::shared_ptr<List<T1>>, std::shared_ptr<List<T1>>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<T1>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<T1>::Nil _args)
                            -> std::pair<std::shared_ptr<List<T1>>,
                                         std::shared_ptr<List<T1>>> {
                          _result = std::make_pair(List<T1>::ctor::Nil_(),
                                                   List<T1>::ctor::Nil_());
                          return {};
                        },
                        [&](const typename List<T1>::Cons _args)
                            -> std::pair<std::shared_ptr<List<T1>>,
                                         std::shared_ptr<List<T1>>> {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<T1>::Nil _args0)
                                      -> std::pair<std::shared_ptr<List<T1>>,
                                                   std::shared_ptr<List<T1>>> {
                                    _result = std::make_pair(
                                        List<T1>::ctor::Cons_(
                                            _args.d_a0, List<T1>::ctor::Nil_()),
                                        List<T1>::ctor::Nil_());
                                    return {};
                                  },
                                  [&](const typename List<T1>::Cons _args0)
                                      -> std::pair<std::shared_ptr<List<T1>>,
                                                   std::shared_ptr<List<T1>>> {
                                    _stack.push_back(_Call1{_args0, _args});
                                    _stack.push_back(_Enter{_args0.d_a1});
                                    return {};
                                  }},
                              _args.d_a1->v());
                          return {};
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<T1>::Cons _args0 = _f._s0;
                const typename List<T1>::Cons _args = _f._s1;
                std::shared_ptr<List<T1>> l1 = _result.first;
                std::shared_ptr<List<T1>> l2 = _result.second;
                _result =
                    std::make_pair(List<T1>::ctor::Cons_(_args.d_a0, l1),
                                   List<T1>::ctor::Cons_(_args0.d_a0, l2));
              }},
          _frame);
    }
    return _result;
  }

  static std::shared_ptr<List<unsigned int>>
  merge_fuel(const unsigned int fuel, std::shared_ptr<List<unsigned int>> l1,
             std::shared_ptr<List<unsigned int>> l2);
  static std::shared_ptr<List<unsigned int>>
  merge(const std::shared_ptr<List<unsigned int>> &l1,
        const std::shared_ptr<List<unsigned int>> &l2);
  static std::shared_ptr<List<unsigned int>>
  merge_sort_fuel(const unsigned int fuel,
                  std::shared_ptr<List<unsigned int>> l);
  static std::shared_ptr<List<unsigned int>>
  merge_sort(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
  partition(const unsigned int pivot,
            const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  quicksort_fuel(const unsigned int fuel,
                 std::shared_ptr<List<unsigned int>> l);
  static std::shared_ptr<List<unsigned int>>
  quicksort(const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static bool
  is_sorted_aux(const unsigned int prev,
                const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static bool
  is_sorted(const std::shared_ptr<List<unsigned int>>
                &l); /// merge_by cmp merges with custom comparator.

  template <MapsTo<bool, unsigned int, unsigned int> F1>
  static std::shared_ptr<List<unsigned int>>
  merge_by_fuel(const unsigned int fuel, F1 &&cmp,
                std::shared_ptr<List<unsigned int>> l1,
                std::shared_ptr<List<unsigned int>> l2) {
    struct _Enter {
      std::shared_ptr<List<unsigned int>> l2;
      std::shared_ptr<List<unsigned int>> l1;
      const unsigned int fuel;
    };

    struct _Call1 {
      decltype(std::declval<const typename List<unsigned int>::Cons &>()
                   .d_a0) _s0;
    };

    struct _Call2 {
      decltype(std::declval<const typename List<unsigned int>::Cons &>()
                   .d_a0) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    std::shared_ptr<List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l2, l1, fuel});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                std::shared_ptr<List<unsigned int>> l2 = _f.l2;
                std::shared_ptr<List<unsigned int>> l1 = _f.l1;
                const unsigned int fuel = _f.fuel;
                if (fuel <= 0) {
                  _result = List<unsigned int>::ctor::Nil_();
                } else {
                  unsigned int f = fuel - 1;
                  std::visit(
                      Overloaded{
                          [&](const typename List<unsigned int>::Nil _args)
                              -> std::shared_ptr<List<unsigned int>> {
                            _result = std::move(l2);
                            return {};
                          },
                          [&](const typename List<unsigned int>::Cons _args)
                              -> std::shared_ptr<List<unsigned int>> {
                            std::visit(
                                Overloaded{
                                    [&](const typename List<unsigned int>::Nil
                                            _args0)
                                        -> std::shared_ptr<List<unsigned int>> {
                                      _result = l1;
                                      return {};
                                    },
                                    [&](const typename List<unsigned int>::Cons
                                            _args0)
                                        -> std::shared_ptr<List<unsigned int>> {
                                      if (cmp(_args.d_a0, _args0.d_a0)) {
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
                _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
              },
              [&](_Call2 _f) {
                _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
              }},
          _frame);
    }
    return _result;
  }

  template <MapsTo<bool, unsigned int, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  merge_by(F0 &&cmp, const std::shared_ptr<List<unsigned int>> &l1,
           const std::shared_ptr<List<unsigned int>> &l2) {
    return merge_by_fuel(
        (len_impl<unsigned int>(l1) + len_impl<unsigned int>(l2)), cmp, l1, l2);
  }

  /// remove_duplicates removes consecutive duplicates from sorted list.
  static std::shared_ptr<List<unsigned int>>
  remove_duplicates(const std::shared_ptr<List<unsigned int>> &l);
  /// uniq_sorted variant that preserves order.
  static std::shared_ptr<List<unsigned int>>
  uniq_sorted_aux(const unsigned int prev, const bool seen,
                  const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  uniq_sorted(const std::shared_ptr<List<unsigned int>> &l);
};

#endif // INCLUDED_LOOPIFY_SORTING
