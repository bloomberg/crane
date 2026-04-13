#ifndef INCLUDED_LOOPIFY_SORTING
#define INCLUDED_LOOPIFY_SORTING

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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
  explicit List(Nil _v) : d_v_(_v) {}

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
              [&](const typename List<t_A>::Nil &) {
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 = m;
                } else {
                  _head = m;
                }
                _continue = false;
              },
              [&](const typename List<t_A>::Cons &_args) {
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
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<T1>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<T1>::Nil &) -> void {
                          _result = 0u;
                        },
                        [&](const typename List<T1>::Cons &_args) -> void {
                          _stack.emplace_back(_Call1{});
                          _stack.emplace_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1) { _result = (_result + 1); }},
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
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<T1>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<T1>::Nil &) -> void {
                          _result =
                              std::make_pair(List<T1>::nil(), List<T1>::nil());
                        },
                        [&](const typename List<T1>::Cons &_args) -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<T1>::Nil &) -> void {
                                    _result = std::make_pair(
                                        List<T1>::cons(_args.d_a0,
                                                       List<T1>::nil()),
                                        List<T1>::nil());
                                  },
                                  [&](const typename List<T1>::Cons &_args0)
                                      -> void {
                                    _stack.emplace_back(_Call1{_args0, _args});
                                    _stack.emplace_back(_Enter{_args0.d_a1});
                                  }},
                              _args.d_a1->v());
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<T1>::Cons _args0 = _f._s0;
                const typename List<T1>::Cons _args = _f._s1;
                const std::shared_ptr<List<T1>> &l1 = _result.first;
                const std::shared_ptr<List<T1>> &l2 = _result.second;
                _result = std::make_pair(List<T1>::cons(_args.d_a0, l1),
                                         List<T1>::cons(_args0.d_a0, l2));
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
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
    std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
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
        unsigned int f = _loop_fuel - 1;
        std::visit(
            Overloaded{
                [&](const typename List<unsigned int>::Nil &) {
                  if (_last) {
                    std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = std::move(_loop_l2);
                  } else {
                    _head = std::move(_loop_l2);
                  }
                  _continue = false;
                },
                [&](const typename List<unsigned int>::Cons &_args) {
                  std::visit(
                      Overloaded{
                          [&](const typename List<unsigned int>::Nil &) {
                            if (_last) {
                              std::get<typename List<unsigned int>::Cons>(
                                  _last->v_mut())
                                  .d_a1 = std::move(_loop_l1);
                            } else {
                              _head = std::move(_loop_l1);
                            }
                            _continue = false;
                          },
                          [&](const typename List<unsigned int>::Cons &_args0) {
                            if (cmp(_args.d_a0, _args0.d_a0)) {
                              auto _cell =
                                  List<unsigned int>::cons(_args.d_a0, nullptr);
                              if (_last) {
                                std::get<typename List<unsigned int>::Cons>(
                                    _last->v_mut())
                                    .d_a1 = _cell;
                              } else {
                                _head = _cell;
                              }
                              _last = _cell;
                              std::shared_ptr<List<unsigned int>> _next_l1 =
                                  _args.d_a1;
                              unsigned int _next_fuel = f;
                              _loop_l1 = std::move(_next_l1);
                              _loop_fuel = std::move(_next_fuel);
                            } else {
                              auto _cell = List<unsigned int>::cons(_args0.d_a0,
                                                                    nullptr);
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
                              unsigned int _next_fuel = f;
                              _loop_l2 = std::move(_next_l2);
                              _loop_fuel = std::move(_next_fuel);
                            }
                          }},
                      _loop_l2->v());
                }},
            _loop_l1->v());
      }
    }
    return _head;
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
