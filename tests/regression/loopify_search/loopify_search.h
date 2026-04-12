#ifndef INCLUDED_LOOPIFY_SEARCH
#define INCLUDED_LOOPIFY_SEARCH

#include <memory>
#include <optional>
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
              [&](const typename List<t_A>::Nil) {
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

/// Consolidated search and optimization algorithms.
struct LoopifySearch {
  /// Internal helper: list length.
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
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<List<T1>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<T1>::Nil) -> void {
                          _result = 0u;
                        },
                        [&](const typename List<T1>::Cons _args) -> void {
                          _stack.push_back(_Call1{});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1) { _result = (_result + 1); }},
          _frame);
    }
    return _result;
  }

  /// knapsack capacity items solves 0/1 knapsack problem.
  /// Items are (weight, value) pairs.
  __attribute__((pure)) static unsigned int knapsack_fuel(
      const unsigned int fuel, const unsigned int capacity,
      const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
          &items);
  __attribute__((pure)) static unsigned int
  knapsack(const unsigned int capacity,
           const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
               &items);
  /// majority l finds majority element using Boyer-Moore algorithm.
  /// Returns (candidate, count).
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  majority(const std::shared_ptr<List<unsigned int>> &l);
  /// longest_increasing_subseq l finds a longest increasing subsequence
  /// (greedy).
  static std::shared_ptr<List<unsigned int>>
  longest_increasing_subseq(const std::shared_ptr<List<unsigned int>> &l);

  /// maximum_by cmp l finds maximum element by custom comparator.
  /// cmp x y returns: 0 if x=y, 1 if x>y, 2 if x<y
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  maximum_by(F0 &&cmp, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      const typename List<unsigned int>::Cons _s0;
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
                const std::shared_ptr<List<unsigned int>> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil) -> void {
                          _result = 0u;
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil)
                                      -> void { _result = _args.d_a0; },
                                  [&](const typename List<unsigned int>::Cons)
                                      -> void {
                                    _stack.push_back(_Call1{_args, cmp});
                                    _stack.push_back(_Enter{_args.d_a1});
                                  }},
                              _args.d_a1->v());
                        }},
                    l->v());
              },
              [&](_Call1 _f) {
                const typename List<unsigned int>::Cons _args = _f._s0;
                F0 cmp = _f._s1;
                unsigned int m = _result;
                if (cmp(_args.d_a0, m) == 1u) {
                  _result = _args.d_a0;
                } else {
                  _result = m;
                }
              }},
          _frame);
    }
    return _result;
  }

  /// Helper for binary search: get nth element.
  __attribute__((pure)) static unsigned int
  nth_impl(const unsigned int n, const std::shared_ptr<List<unsigned int>> &l);
  /// Helper for binary search: take first k elements.
  static std::shared_ptr<List<unsigned int>>
  take_impl(const unsigned int k, const std::shared_ptr<List<unsigned int>> &l);
  /// Helper for binary search: drop first k elements.
  static std::shared_ptr<List<unsigned int>>
  drop_impl(const unsigned int k, std::shared_ptr<List<unsigned int>> l);
  /// binary_search_fuel target sorted_list searches for target in sorted list.
  /// Returns true if found.
  __attribute__((pure)) static bool
  binary_search_fuel(const unsigned int fuel, const unsigned int target,
                     const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static bool
  binary_search(const unsigned int target,
                const std::shared_ptr<List<unsigned int>> &l);
  /// longest_run l finds the longest run of consecutive equal elements.
  static std::shared_ptr<List<unsigned int>>
  longest_run_aux(std::shared_ptr<List<unsigned int>> current_run,
                  std::shared_ptr<List<unsigned int>> best_run,
                  const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<unsigned int>>
  longest_run(const std::shared_ptr<List<unsigned int>> &l);
  /// collatz n computes Collatz sequence length (not the list).
  __attribute__((pure)) static unsigned int
  collatz_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int collatz(const unsigned int n);
  /// lis l simple longest increasing subsequence (greedy approach).
  static std::shared_ptr<List<unsigned int>>
  lis(const std::shared_ptr<List<unsigned int>> &l);
  /// subset_sum target l checks if any subset sums to target.
  __attribute__((pure)) static bool
  subset_sum_fuel(const unsigned int fuel, const unsigned int target,
                  const std::shared_ptr<List<unsigned int>> &l);
  __attribute__((pure)) static bool
  subset_sum(const unsigned int target,
             const std::shared_ptr<List<unsigned int>> &l);

  /// Helper: filter predicate.
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  filter_impl(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil) {
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
                  _loop_l = _args.d_a1;
                }
              }},
          _loop_l->v());
    }
    return _head;
  }

  /// sieve l removes multiples (simplified sieve of Eratosthenes).
  static std::shared_ptr<List<unsigned int>>
  sieve_fuel(const unsigned int fuel, std::shared_ptr<List<unsigned int>> l);
  static std::shared_ptr<List<unsigned int>>
  sieve(const std::shared_ptr<List<unsigned int>> &l);
  /// Helper: check if element is in list.
  __attribute__((pure)) static bool
  elem_impl(const unsigned int x, const std::shared_ptr<List<unsigned int>> &l);
  /// nub l removes duplicates from list.
  static std::shared_ptr<List<unsigned int>>
  nub_fuel(const unsigned int fuel, std::shared_ptr<List<unsigned int>> l);
  static std::shared_ptr<List<unsigned int>>
  nub(const std::shared_ptr<List<unsigned int>> &l);
  /// remove_duplicates l removes all duplicate elements.
  static std::shared_ptr<List<unsigned int>>
  remove_duplicates_fuel(const unsigned int fuel,
                         std::shared_ptr<List<unsigned int>> l);
  static std::shared_ptr<List<unsigned int>>
  remove_duplicates(const std::shared_ptr<List<unsigned int>> &l);
  /// quicksort l sorts list using quicksort with filter-based partitioning.
  static std::shared_ptr<List<unsigned int>>
  quicksort_fuel(const unsigned int fuel,
                 std::shared_ptr<List<unsigned int>> l);
  static std::shared_ptr<List<unsigned int>>
  quicksort(const std::shared_ptr<List<unsigned int>> &l);
  /// Helper: split list into two roughly equal parts.
  __attribute__((pure)) static std::pair<std::shared_ptr<List<unsigned int>>,
                                         std::shared_ptr<List<unsigned int>>>
  split_list(const std::shared_ptr<List<unsigned int>> &l);
  /// Helper: merge two sorted lists with fuel.
  static std::shared_ptr<List<unsigned int>>
  merge_sorted_fuel(const unsigned int fuel,
                    std::shared_ptr<List<unsigned int>> l1,
                    std::shared_ptr<List<unsigned int>> l2);
  static std::shared_ptr<List<unsigned int>>
  merge_sorted(const std::shared_ptr<List<unsigned int>> &l1,
               const std::shared_ptr<List<unsigned int>> &l2);
  /// merge_sort l sorts list using merge sort.
  static std::shared_ptr<List<unsigned int>>
  merge_sort_fuel(const unsigned int fuel,
                  std::shared_ptr<List<unsigned int>> l);
  static std::shared_ptr<List<unsigned int>>
  merge_sort(const std::shared_ptr<List<unsigned int>> &l);
  /// Helper: remove first occurrence of x from list.
  static std::shared_ptr<List<unsigned int>>
  remove_first(const unsigned int x,
               const std::shared_ptr<List<unsigned int>> &l);

  /// Helper: map function over list and concatenate results.
  template <MapsTo<std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>,
                   unsigned int>
                F0>
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  concat_map(F0 &&f, const std::shared_ptr<List<unsigned int>> &l) {
    struct _Enter {
      const std::shared_ptr<List<unsigned int>> l;
    };

    struct _Call1 {
      std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
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
                        [&](const typename List<unsigned int>::Nil) -> void {
                          _result =
                              List<std::shared_ptr<List<unsigned int>>>::nil();
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          _stack.push_back(_Call1{f(_args.d_a0)});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    l->v());
              },
              [&](_Call1 _f) { _result = _f._s0->app(_result); }},
          _frame);
    }
    return _result;
  }

  /// Helper: map function that prepends element to each list.
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> map_cons(
      const unsigned int x,
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &lsts);
  /// perms_choices_fuel fuel choices orig generates permutations by iterating
  /// over choices.  Single self-recursive function for full loopification.
  /// Match on remaining is hoisted out of let-binding.
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  perms_choices_fuel(const unsigned int fuel,
                     const std::shared_ptr<List<unsigned int>> &choices,
                     const std::shared_ptr<List<unsigned int>> &orig);
  /// permutations_fuel fuel l generates all permutations of list.
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  permutations_fuel(const unsigned int fuel,
                    const std::shared_ptr<List<unsigned int>> &l);
  static std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
  permutations(const std::shared_ptr<List<unsigned int>> &l);
  /// linear_search x l finds index of first occurrence of x.
  __attribute__((pure)) static std::optional<unsigned int>
  linear_search_aux(const unsigned int x,
                    const std::shared_ptr<List<unsigned int>> &l,
                    const unsigned int idx);
  __attribute__((pure)) static std::optional<unsigned int>
  linear_search(const unsigned int x,
                const std::shared_ptr<List<unsigned int>> &l);
  /// all_indices x l finds all indices where x occurs.
  static std::shared_ptr<List<unsigned int>>
  all_indices_aux(const unsigned int x,
                  const std::shared_ptr<List<unsigned int>> &l,
                  const unsigned int idx);
  static std::shared_ptr<List<unsigned int>>
  all_indices(const unsigned int x,
              const std::shared_ptr<List<unsigned int>> &l);
  /// min_element l finds minimum element in list.
  __attribute__((pure)) static unsigned int
  min_element(const std::shared_ptr<List<unsigned int>> &l);

  /// Binary tree for search operations.
  struct btree {
    // TYPES
    struct BLeaf {
      unsigned int d_a0;
    };

    struct BNode {
      std::shared_ptr<btree> d_a0;
      std::shared_ptr<btree> d_a1;
    };

    using variant_t = std::variant<BLeaf, BNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit btree(BLeaf _v) : d_v_(std::move(_v)) {}

    explicit btree(BNode _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<btree> bleaf(unsigned int a0) {
      return std::make_shared<btree>(BLeaf{std::move(a0)});
    }

    static std::shared_ptr<btree> bnode(const std::shared_ptr<btree> &a0,
                                        const std::shared_ptr<btree> &a1) {
      return std::make_shared<btree>(BNode{a0, a1});
    }

    static std::shared_ptr<btree> bnode(std::shared_ptr<btree> &&a0,
                                        std::shared_ptr<btree> &&a1) {
      return std::make_shared<btree>(BNode{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<btree>, T1, std::shared_ptr<btree>, T1> F1>
  static T1 btree_rect(F0 &&f, F1 &&f0, const std::shared_ptr<btree> &b) {
    struct _Enter {
      const std::shared_ptr<btree> b;
    };

    struct _Call1 {
      decltype(std::declval<const typename btree::BNode &>().d_a0) _s0;
      decltype(std::declval<const typename btree::BNode &>().d_a1) _s1;
      decltype(std::declval<const typename btree::BNode &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename btree::BNode &>().d_a1) _s1;
      decltype(std::declval<const typename btree::BNode &>().d_a0) _s2;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{b});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
                       const std::shared_ptr<btree> b = _f.b;
                       std::visit(
                           Overloaded{
                               [&](const typename btree::BLeaf _args) -> void {
                                 _result = f(_args.d_a0);
                               },
                               [&](const typename btree::BNode _args) -> void {
                                 _stack.push_back(_Call1{_args.d_a0, _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a1});
                               }},
                           b->v());
                     },
                     [&](_Call1 _f) {
                       _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                       _stack.push_back(_Enter{_f._s0});
                     },
                     [&](_Call2 _f) {
                       _result = f0(_f._s2, _result, _f._s1, _f._s0);
                     }},
          _frame);
    }
    return _result;
  }

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<btree>, T1, std::shared_ptr<btree>, T1> F1>
  static T1 btree_rec(F0 &&f, F1 &&f0, const std::shared_ptr<btree> &b) {
    struct _Enter {
      const std::shared_ptr<btree> b;
    };

    struct _Call1 {
      decltype(std::declval<const typename btree::BNode &>().d_a0) _s0;
      decltype(std::declval<const typename btree::BNode &>().d_a1) _s1;
      decltype(std::declval<const typename btree::BNode &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename btree::BNode &>().d_a1) _s1;
      decltype(std::declval<const typename btree::BNode &>().d_a0) _s2;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{b});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
                       const std::shared_ptr<btree> b = _f.b;
                       std::visit(
                           Overloaded{
                               [&](const typename btree::BLeaf _args) -> void {
                                 _result = f(_args.d_a0);
                               },
                               [&](const typename btree::BNode _args) -> void {
                                 _stack.push_back(_Call1{_args.d_a0, _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a1});
                               }},
                           b->v());
                     },
                     [&](_Call1 _f) {
                       _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                       _stack.push_back(_Enter{_f._s0});
                     },
                     [&](_Call2 _f) {
                       _result = f0(_f._s2, _result, _f._s1, _f._s0);
                     }},
          _frame);
    }
    return _result;
  }

  /// or_search p t searches tree with || recursion.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool or_search(F0 &&p,
                                              const std::shared_ptr<btree> &t) {
    struct _Enter {
      const std::shared_ptr<btree> t;
    };

    struct _Call1 {
      decltype(std::declval<const typename btree::BNode &>().d_a0) _s0;
    };

    struct _Call2 {
      bool _s0;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2>;
    bool _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{t});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{[&](_Enter _f) {
                       const std::shared_ptr<btree> t = _f.t;
                       std::visit(
                           Overloaded{
                               [&](const typename btree::BLeaf _args) -> void {
                                 _result = p(_args.d_a0);
                               },
                               [&](const typename btree::BNode _args) -> void {
                                 _stack.push_back(_Call1{_args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a1});
                               }},
                           t->v());
                     },
                     [&](_Call1 _f) {
                       _stack.push_back(_Call2{_result});
                       _stack.push_back(_Enter{_f._s0});
                     },
                     [&](_Call2 _f) { _result = (_result || _f._s0); }},
          _frame);
    }
    return _result;
  }

  /// find_indices p l finds all indices where predicate holds.
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  find_indices_aux(F0 &&p, const std::shared_ptr<List<unsigned int>> &l,
                   const unsigned int idx) {
    std::shared_ptr<List<unsigned int>> _head{};
    std::shared_ptr<List<unsigned int>> _last{};
    unsigned int _loop_idx = idx;
    std::shared_ptr<List<unsigned int>> _loop_l = l;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil) {
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
                  auto _cell = List<unsigned int>::cons(_loop_idx, nullptr);
                  if (_last) {
                    std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                        .d_a1 = _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  unsigned int _next_idx = (_loop_idx + 1);
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  _loop_idx = std::move(_next_idx);
                  _loop_l = std::move(_next_l);
                } else {
                  unsigned int _next_idx = (_loop_idx + 1);
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  _loop_idx = std::move(_next_idx);
                  _loop_l = std::move(_next_l);
                }
              }},
          _loop_l->v());
    }
    return _head;
  }

  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<List<unsigned int>>
  find_indices(F0 &&p, const std::shared_ptr<List<unsigned int>> &l) {
    return find_indices_aux(p, l, 0u);
  }
};

#endif // INCLUDED_LOOPIFY_SEARCH
