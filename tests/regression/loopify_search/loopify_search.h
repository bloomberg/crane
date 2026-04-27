#ifndef INCLUDED_LOOPIFY_SEARCH
#define INCLUDED_LOOPIFY_SEARCH

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    std::unique_ptr<List<t_A>> _head{};
    std::unique_ptr<List<t_A>> *_write = &_head;
    const List *_loop_self = this;
    while (true) {
      auto &&_sv = *(_loop_self);
      if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
        *(_write) = std::make_unique<List<t_A>>(m);
        break;
      } else {
        const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
        auto _cell = std::make_unique<List<t_A>>(
            typename List<t_A>::Cons(d_a0, nullptr));
        *(_write) = std::move(_cell);
        _write = &std::get<typename List<t_A>::Cons>((*_write)->v_mut()).d_a1;
        _loop_self = d_a1.get();
        continue;
      }
    }
    return std::move(*(_head));
  }
};

/// Consolidated search and optimization algorithms.
struct LoopifySearch {
  /// Internal helper: list length.
  template <typename T1>
  __attribute__((pure)) static unsigned int len_impl(const List<T1> &l) {
    struct _Enter {
      const List<T1> l;
    };

    struct _Call1 {};

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> l = _f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Call1{});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = (_result + 1);
      }
    }
    return _result;
  }

  /// knapsack capacity items solves 0/1 knapsack problem.
  /// Items are (weight, value) pairs.
  __attribute__((pure)) static unsigned int
  knapsack_fuel(const unsigned int &fuel, const unsigned int &capacity,
                const List<std::pair<unsigned int, unsigned int>> &items);
  __attribute__((pure)) static unsigned int
  knapsack(const unsigned int &capacity,
           const List<std::pair<unsigned int, unsigned int>> &items);
  /// majority l finds majority element using Boyer-Moore algorithm.
  /// Returns (candidate, count).
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  majority(const List<unsigned int> &l);
  /// longest_increasing_subseq l finds a longest increasing subsequence
  /// (greedy).
  __attribute__((pure)) static List<unsigned int>
  longest_increasing_subseq(const List<unsigned int> &l);

  /// maximum_by cmp l finds maximum element by custom comparator.
  /// cmp x y returns: 0 if x=y, 1 if x>y, 2 if x<y
  template <MapsTo<unsigned int, unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  maximum_by(F0 &&cmp, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      F0 _s0;
      unsigned int _s1;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = 0u;
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          auto &&_sv = *(d_a1);
          if (std::holds_alternative<typename List<unsigned int>::Nil>(
                  _sv.v())) {
            _result = d_a0;
          } else {
            _stack.emplace_back(_Call1{cmp, d_a0});
            _stack.emplace_back(_Enter{*(d_a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        F0 cmp = _f._s0;
        unsigned int d_a0 = _f._s1;
        unsigned int m = _result;
        if (cmp(d_a0, m) == 1u) {
          _result = d_a0;
        } else {
          _result = m;
        }
      }
    }
    return _result;
  }

  /// Helper for binary search: get nth element.
  __attribute__((pure)) static unsigned int
  nth_impl(const unsigned int &n, const List<unsigned int> &l);
  /// Helper for binary search: take first k elements.
  __attribute__((pure)) static List<unsigned int>
  take_impl(const unsigned int &k, const List<unsigned int> &l);
  /// Helper for binary search: drop first k elements.
  __attribute__((pure)) static List<unsigned int>
  drop_impl(const unsigned int &k, List<unsigned int> l);
  /// binary_search_fuel target sorted_list searches for target in sorted list.
  /// Returns true if found.
  __attribute__((pure)) static bool
  binary_search_fuel(const unsigned int &fuel, const unsigned int &target,
                     const List<unsigned int> &l);
  __attribute__((pure)) static bool binary_search(const unsigned int &target,
                                                  const List<unsigned int> &l);
  /// longest_run l finds the longest run of consecutive equal elements.
  __attribute__((pure)) static List<unsigned int>
  longest_run_aux(List<unsigned int> current_run, List<unsigned int> best_run,
                  const List<unsigned int> &l);
  __attribute__((pure)) static List<unsigned int>
  longest_run(const List<unsigned int> &l);
  /// collatz n computes Collatz sequence length (not the list).
  __attribute__((pure)) static unsigned int
  collatz_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int collatz(const unsigned int &n);
  /// lis l simple longest increasing subsequence (greedy approach).
  __attribute__((pure)) static List<unsigned int>
  lis(const List<unsigned int> &l);
  /// subset_sum target l checks if any subset sums to target.
  __attribute__((pure)) static bool
  subset_sum_fuel(const unsigned int &fuel, const unsigned int &target,
                  const List<unsigned int> &l);
  __attribute__((pure)) static bool subset_sum(const unsigned int &target,
                                               const List<unsigned int> &l);

  /// Helper: filter predicate.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  filter_impl(F0 &&p, const List<unsigned int> &l) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      if (p(d_a0)) {
        return List<unsigned int>::cons(d_a0, filter_impl(p, *(d_a1)));
      } else {
        return filter_impl(p, *(d_a1));
      }
    }
  }

  /// sieve l removes multiples (simplified sieve of Eratosthenes).
  __attribute__((pure)) static List<unsigned int>
  sieve_fuel(const unsigned int &fuel, List<unsigned int> l);
  __attribute__((pure)) static List<unsigned int>
  sieve(const List<unsigned int> &l);
  /// Helper: check if element is in list.
  __attribute__((pure)) static bool elem_impl(const unsigned int &x,
                                              const List<unsigned int> &l);
  /// nub l removes duplicates from list.
  __attribute__((pure)) static List<unsigned int>
  nub_fuel(const unsigned int &fuel, List<unsigned int> l);
  __attribute__((pure)) static List<unsigned int>
  nub(const List<unsigned int> &l);
  /// remove_duplicates l removes all duplicate elements.
  __attribute__((pure)) static List<unsigned int>
  remove_duplicates_fuel(const unsigned int &fuel, List<unsigned int> l);
  __attribute__((pure)) static List<unsigned int>
  remove_duplicates(const List<unsigned int> &l);
  /// quicksort l sorts list using quicksort with filter-based partitioning.
  __attribute__((pure)) static List<unsigned int>
  quicksort_fuel(const unsigned int &fuel, List<unsigned int> l);
  __attribute__((pure)) static List<unsigned int>
  quicksort(const List<unsigned int> &l);
  /// Helper: split list into two roughly equal parts.
  __attribute__((pure)) static std::pair<List<unsigned int>, List<unsigned int>>
  split_list(const List<unsigned int> &l);
  /// Helper: merge two sorted lists with fuel.
  __attribute__((pure)) static List<unsigned int>
  merge_sorted_fuel(const unsigned int &fuel, List<unsigned int> l1,
                    List<unsigned int> l2);
  __attribute__((pure)) static List<unsigned int>
  merge_sorted(const List<unsigned int> &l1, const List<unsigned int> &l2);
  /// merge_sort l sorts list using merge sort.
  __attribute__((pure)) static List<unsigned int>
  merge_sort_fuel(const unsigned int &fuel, List<unsigned int> l);
  __attribute__((pure)) static List<unsigned int>
  merge_sort(const List<unsigned int> &l);
  /// Helper: remove first occurrence of x from list.
  __attribute__((pure)) static List<unsigned int>
  remove_first(const unsigned int &x, const List<unsigned int> &l);

  /// Helper: map function over list and concatenate results.
  template <MapsTo<List<List<unsigned int>>, unsigned int> F0>
  __attribute__((pure)) static List<List<unsigned int>>
  concat_map(F0 &&f, const List<unsigned int> &l) {
    struct _Enter {
      const List<unsigned int> l;
    };

    struct _Call1 {
      List<List<unsigned int>> _s0;
    };

    using _Frame = std::variant<_Enter, _Call1>;
    List<List<unsigned int>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(16);
    _stack.emplace_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<unsigned int> l = _f.l;
        if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
          _result = List<List<unsigned int>>::nil();
        } else {
          const auto &[d_a0, d_a1] =
              std::get<typename List<unsigned int>::Cons>(l.v());
          _stack.emplace_back(_Call1{f(d_a0)});
          _stack.emplace_back(_Enter{*(d_a1)});
        }
      } else {
        auto _f = std::move(std::get<_Call1>(_frame));
        _result = _f._s0.app(_result);
      }
    }
    return _result;
  }

  /// Helper: map function that prepends element to each list.
  __attribute__((pure)) static List<List<unsigned int>>
  map_cons(unsigned int x, const List<List<unsigned int>> &lsts);
  /// perms_choices_fuel fuel choices orig generates permutations by iterating
  /// over choices.  Single self-recursive function for full loopification.
  /// Match on remaining is hoisted out of let-binding.
  __attribute__((pure)) static List<List<unsigned int>>
  perms_choices_fuel(const unsigned int &fuel,
                     const List<unsigned int> &choices,
                     const List<unsigned int> &orig);
  /// permutations_fuel fuel l generates all permutations of list.
  __attribute__((pure)) static List<List<unsigned int>>
  permutations_fuel(const unsigned int &fuel, const List<unsigned int> &l);
  __attribute__((pure)) static List<List<unsigned int>>
  permutations(const List<unsigned int> &l);
  /// linear_search x l finds index of first occurrence of x.
  __attribute__((pure)) static std::optional<unsigned int>
  linear_search_aux(const unsigned int &x, const List<unsigned int> &l,
                    unsigned int idx);
  __attribute__((pure)) static std::optional<unsigned int>
  linear_search(const unsigned int &x, const List<unsigned int> &l);
  /// all_indices x l finds all indices where x occurs.
  __attribute__((pure)) static List<unsigned int>
  all_indices_aux(const unsigned int &x, const List<unsigned int> &l,
                  unsigned int idx);
  __attribute__((pure)) static List<unsigned int>
  all_indices(const unsigned int &x, const List<unsigned int> &l);
  /// min_element l finds minimum element in list.
  __attribute__((pure)) static unsigned int
  min_element(const List<unsigned int> &l);

  /// Binary tree for search operations.
  struct btree {
    // TYPES
    struct BLeaf {
      unsigned int d_a0;
    };

    struct BNode {
      std::unique_ptr<btree> d_a0;
      std::unique_ptr<btree> d_a1;
    };

    using variant_t = std::variant<BLeaf, BNode>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    btree() {}

    explicit btree(BLeaf _v) : d_v_(std::move(_v)) {}

    explicit btree(BNode _v) : d_v_(std::move(_v)) {}

    btree(const btree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    btree(btree &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) btree &operator=(const btree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) btree &operator=(btree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) btree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<BLeaf>(_sv.v())) {
        const auto &[d_a0] = std::get<BLeaf>(_sv.v());
        return btree(BLeaf{d_a0});
      } else {
        const auto &[d_a0, d_a1] = std::get<BNode>(_sv.v());
        return btree(
            BNode{d_a0 ? std::make_unique<LoopifySearch::btree>(d_a0->clone())
                       : nullptr,
                  d_a1 ? std::make_unique<LoopifySearch::btree>(d_a1->clone())
                       : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static btree bleaf(unsigned int a0) {
      return btree(BLeaf{std::move(a0)});
    }

    __attribute__((pure)) static btree bnode(const btree &a0, const btree &a1) {
      return btree(
          BNode{std::make_unique<btree>(a0), std::make_unique<btree>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) btree *operator->() { return this; }

    __attribute__((pure)) const btree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = btree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, btree, T1, btree, T1> F1>
  static T1 btree_rect(F0 &&f, F1 &&f0, const btree &b) {
    if (std::holds_alternative<typename btree::BLeaf>(b.v())) {
      const auto &[d_a0] = std::get<typename btree::BLeaf>(b.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename btree::BNode>(b.v());
      return f0(*(d_a0), btree_rect<T1>(f, f0, *(d_a0)), *(d_a1),
                btree_rect<T1>(f, f0, *(d_a1)));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, btree, T1, btree, T1> F1>
  static T1 btree_rec(F0 &&f, F1 &&f0, const btree &b) {
    if (std::holds_alternative<typename btree::BLeaf>(b.v())) {
      const auto &[d_a0] = std::get<typename btree::BLeaf>(b.v());
      return f(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename btree::BNode>(b.v());
      return f0(*(d_a0), btree_rec<T1>(f, f0, *(d_a0)), *(d_a1),
                btree_rec<T1>(f, f0, *(d_a1)));
    }
  }

  /// or_search p t searches tree with || recursion.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static bool or_search(F0 &&p, const btree &t) {
    if (std::holds_alternative<typename btree::BLeaf>(t.v())) {
      const auto &[d_a0] = std::get<typename btree::BLeaf>(t.v());
      return p(d_a0);
    } else {
      const auto &[d_a0, d_a1] = std::get<typename btree::BNode>(t.v());
      return (or_search(p, *(d_a0)) || or_search(p, *(d_a1)));
    }
  }

  /// find_indices p l finds all indices where predicate holds.
  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  find_indices_aux(F0 &&p, const List<unsigned int> &l, unsigned int idx) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v());
      if (p(d_a0)) {
        return List<unsigned int>::cons(
            idx, find_indices_aux(p, *(d_a1), (idx + 1)));
      } else {
        return find_indices_aux(p, *(d_a1), (idx + 1));
      }
    }
  }

  template <MapsTo<bool, unsigned int> F0>
  __attribute__((pure)) static List<unsigned int>
  find_indices(F0 &&p, const List<unsigned int> &l) {
    return find_indices_aux(p, l, 0u);
  }
};

#endif // INCLUDED_LOOPIFY_SEARCH
