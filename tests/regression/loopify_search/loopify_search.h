#ifndef INCLUDED_LOOPIFY_SEARCH
#define INCLUDED_LOOPIFY_SEARCH

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::unique_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_unique<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_unique<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    std::unique_ptr<List<A>> _head{};
    std::unique_ptr<List<A>> *_write = &_head;
    const List *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_unique<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_unique<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
        _loop_self = a1.get();
        continue;
      }
    }
    return std::move(*_head);
  }
};

/// Consolidated search and optimization algorithms.
struct LoopifySearch {
  /// Internal helper: list length.
  template <typename T1>
  static uint64_t
  len_impl(const List<T1> &l) { /// _Enter: captures varying parameters for each
                                /// recursive call.

    struct _Enter {
      const List<T1> *l;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified len_impl: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (_result + 1);
      }
    }
    return _result;
  }

  /// knapsack capacity items solves 0/1 knapsack problem.
  /// Items are (weight, value) pairs.
  static uint64_t
  knapsack_fuel(uint64_t fuel, uint64_t capacity,
                const List<std::pair<uint64_t, uint64_t>> &items);
  static uint64_t knapsack(uint64_t capacity,
                           const List<std::pair<uint64_t, uint64_t>> &items);
  /// majority l finds majority element using Boyer-Moore algorithm.
  /// Returns (candidate, count).
  static std::pair<uint64_t, uint64_t> majority(const List<uint64_t> &l);
  /// longest_increasing_subseq l finds a longest increasing subsequence
  /// (greedy).
  static List<uint64_t> longest_increasing_subseq(const List<uint64_t> &l);

  /// maximum_by cmp l finds maximum element by custom comparator.
  /// cmp x y returns: 0 if x=y, 1 if x>y, 2 if x<y
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static uint64_t
  maximum_by(F0 &&cmp,
             const List<uint64_t> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Cont_Cons: saves [a0, cmp], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Cons {
      uint64_t a0;
      F0 cmp;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified maximum_by: _Enter -> _Cont_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
            _result = std::move(a0);
          } else {
            _stack.emplace_back(_Cont_Cons{a0, cmp});
            _stack.emplace_back(_Enter{a1.get()});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        F0 cmp = _f.cmp;
        uint64_t m = _result;
        if (cmp(a0, m) == UINT64_C(1)) {
          _result = std::move(a0);
        } else {
          _result = std::move(m);
        }
      }
    }
    return _result;
  }

  /// Helper for binary search: get nth element.
  static uint64_t nth_impl(uint64_t n, const List<uint64_t> &l);
  /// Helper for binary search: take first k elements.
  static List<uint64_t> take_impl(uint64_t k, const List<uint64_t> &l);
  /// Helper for binary search: drop first k elements.
  static List<uint64_t> drop_impl(uint64_t k, List<uint64_t> l);
  /// binary_search_fuel target sorted_list searches for target in sorted list.
  /// Returns true if found.
  static bool binary_search_fuel(uint64_t fuel, uint64_t target,
                                 const List<uint64_t> &l);
  static bool binary_search(uint64_t target, const List<uint64_t> &l);
  /// longest_run l finds the longest run of consecutive equal elements.
  static List<uint64_t> longest_run_aux(List<uint64_t> current_run,
                                        List<uint64_t> best_run,
                                        const List<uint64_t> &l);
  static List<uint64_t> longest_run(const List<uint64_t> &l);
  /// collatz n computes Collatz sequence length (not the list).
  static uint64_t collatz_fuel(uint64_t fuel, uint64_t n);
  static uint64_t collatz(uint64_t n);
  /// lis l simple longest increasing subsequence (greedy approach).
  static List<uint64_t> lis(const List<uint64_t> &l);
  /// subset_sum target l checks if any subset sums to target.
  static bool subset_sum_fuel(uint64_t fuel, uint64_t target,
                              const List<uint64_t> &l);
  static bool subset_sum(uint64_t target,
                         const List<uint64_t> &l); /// Helper: filter predicate.

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t> filter_impl(F0 &&p, const List<uint64_t> &l) {
    std::unique_ptr<List<uint64_t>> _head{};
    std::unique_ptr<List<uint64_t>> *_write = &_head;
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell = std::make_unique<List<uint64_t>>(
              typename List<uint64_t>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_l = a1.get();
          continue;
        } else {
          _loop_l = a1.get();
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  /// sieve l removes multiples (simplified sieve of Eratosthenes).
  static List<uint64_t> sieve_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> sieve(const List<uint64_t> &l);
  /// Helper: check if element is in list.
  static bool elem_impl(uint64_t x, const List<uint64_t> &l);
  /// nub l removes duplicates from list.
  static List<uint64_t> nub_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> nub(const List<uint64_t> &l);
  /// remove_duplicates l removes all duplicate elements.
  static List<uint64_t> remove_duplicates_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> remove_duplicates(const List<uint64_t> &l);
  /// quicksort l sorts list using quicksort with filter-based partitioning.
  static List<uint64_t> quicksort_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> quicksort(const List<uint64_t> &l);
  /// Helper: split list into two roughly equal parts.
  static std::pair<List<uint64_t>, List<uint64_t>>
  split_list(const List<uint64_t> &l);
  /// Helper: merge two sorted lists with fuel.
  static List<uint64_t> merge_sorted_fuel(uint64_t fuel, List<uint64_t> l1,
                                          List<uint64_t> l2);
  static List<uint64_t> merge_sorted(const List<uint64_t> &l1,
                                     const List<uint64_t> &l2);
  /// merge_sort l sorts list using merge sort.
  static List<uint64_t> merge_sort_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> merge_sort(const List<uint64_t> &l);
  /// Helper: remove first occurrence of x from list.
  static List<uint64_t> remove_first(uint64_t x, const List<uint64_t> &l);

  /// Helper: map function over list and concatenate results.
  template <typename F0>
    requires std::is_invocable_r_v<List<List<uint64_t>>, F0 &, uint64_t &>
  static List<List<uint64_t>>
  concat_map(F0 &&f,
             const List<uint64_t> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      List<List<uint64_t>> a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<List<uint64_t>> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&l});
    /// Loopified concat_map: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<List<uint64_t>>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{f(a0)});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = _f.a0.app(_result);
      }
    }
    return _result;
  }

  /// Helper: map function that prepends element to each list.
  static List<List<uint64_t>> map_cons(uint64_t x,
                                       const List<List<uint64_t>> &lsts);
  /// perms_choices_fuel fuel choices orig generates permutations by iterating
  /// over choices.  Single self-recursive function for full loopification.
  /// Match on remaining is hoisted out of let-binding.
  static List<List<uint64_t>> perms_choices_fuel(uint64_t fuel,
                                                 const List<uint64_t> &choices,
                                                 const List<uint64_t> &orig);
  /// permutations_fuel fuel l generates all permutations of list.
  static List<List<uint64_t>> permutations_fuel(uint64_t fuel,
                                                const List<uint64_t> &l);
  static List<List<uint64_t>> permutations(const List<uint64_t> &l);
  /// linear_search x l finds index of first occurrence of x.
  static std::optional<uint64_t>
  linear_search_aux(uint64_t x, const List<uint64_t> &l, uint64_t idx);
  static std::optional<uint64_t> linear_search(uint64_t x,
                                               const List<uint64_t> &l);
  /// all_indices x l finds all indices where x occurs.
  static List<uint64_t> all_indices_aux(uint64_t x, const List<uint64_t> &l,
                                        uint64_t idx);
  static List<uint64_t> all_indices(uint64_t x, const List<uint64_t> &l);
  /// min_element l finds minimum element in list.
  static uint64_t min_element(const List<uint64_t> &l);

  /// Binary tree for search operations.
  struct btree {
    // TYPES
    struct BLeaf {
      uint64_t a0;
    };

    struct BNode {
      std::unique_ptr<btree> a0;
      std::unique_ptr<btree> a1;
    };

    using variant_t = std::variant<BLeaf, BNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    btree() {}

    explicit btree(BLeaf _v) : v_(std::move(_v)) {}

    explicit btree(BNode _v) : v_(std::move(_v)) {}

    btree(const btree &_other) : v_(std::move(_other.clone().v_)) {}

    btree(btree &&_other) noexcept : v_(std::move(_other.v_)) {}

    btree &operator=(const btree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    btree &operator=(btree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    btree clone() const {
      btree _out{};

      struct _CloneFrame {
        const btree *_src;
        btree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const btree *_src = _frame._src;
        btree *_dst = _frame._dst;
        if (std::holds_alternative<BLeaf>(_src->v())) {
          const auto &_alt = std::get<BLeaf>(_src->v());
          _dst->v_ = BLeaf{_alt.a0};
        } else {
          const auto &_alt = std::get<BNode>(_src->v());
          _dst->v_ = BNode{_alt.a0 ? std::make_unique<btree>() : nullptr,
                           _alt.a1 ? std::make_unique<btree>() : nullptr};
          auto &_dst_alt = std::get<BNode>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static btree bleaf(uint64_t a0) { return btree(BLeaf{a0}); }

    static btree bnode(btree a0, btree a1) {
      return btree(BNode{std::make_unique<btree>(std::move(a0)),
                         std::make_unique<btree>(std::move(a1))});
    }

    // MANIPULATORS
    ~btree() {
      std::vector<std::unique_ptr<btree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](btree &_node) {
        if (std::holds_alternative<BNode>(_node.v_)) {
          auto &_alt = std::get<BNode>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, btree &, T1 &, btree &, T1 &>
  static T1 btree_rect(F0 &&f, F1 &&f0,
                       const btree &b) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

    struct _Enter {
      const btree *b;
    };

    /// _After_BNode: saves [a0_0, a1, a0_1], dispatches next recursive call.
    struct _After_BNode {
      const btree *a0_0;
      btree a1;
      btree a0_1;
    };

    /// _Combine_BNode: receives partial results, combines with _result from
    /// final call.
    struct _Combine_BNode {
      T1 _result;
      btree a1;
      btree a0;
    };

    using _Frame = std::variant<_Enter, _After_BNode, _Combine_BNode>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&b});
    /// Loopified btree_rect: _Enter -> _After_BNode -> _Combine_BNode.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const btree &b = *_f.b;
        if (std::holds_alternative<typename btree::BLeaf>(b.v())) {
          const auto &[a0] = std::get<typename btree::BLeaf>(b.v());
          _result = f(a0);
        } else {
          const auto &[a0, a1] = std::get<typename btree::BNode>(b.v());
          _stack.emplace_back(_After_BNode{a0.get(), *a1, *a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else if (std::holds_alternative<_After_BNode>(_frame)) {
        auto _f = std::move(std::get<_After_BNode>(_frame));
        _stack.emplace_back(_Combine_BNode{std::move(_result), std::move(_f.a1),
                                           std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_BNode>(_frame));
        _result = f0(_f.a0, std::move(_result), _f.a1, std::move(_f._result));
      }
    }
    return _result;
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, btree &, T1 &, btree &, T1 &>
  static T1 btree_rec(F0 &&f, F1 &&f0,
                      const btree &b) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const btree *b;
    };

    /// _After_BNode: saves [a0_0, a1, a0_1], dispatches next recursive call.
    struct _After_BNode {
      const btree *a0_0;
      btree a1;
      btree a0_1;
    };

    /// _Combine_BNode: receives partial results, combines with _result from
    /// final call.
    struct _Combine_BNode {
      T1 _result;
      btree a1;
      btree a0;
    };

    using _Frame = std::variant<_Enter, _After_BNode, _Combine_BNode>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&b});
    /// Loopified btree_rec: _Enter -> _After_BNode -> _Combine_BNode.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const btree &b = *_f.b;
        if (std::holds_alternative<typename btree::BLeaf>(b.v())) {
          const auto &[a0] = std::get<typename btree::BLeaf>(b.v());
          _result = f(a0);
        } else {
          const auto &[a0, a1] = std::get<typename btree::BNode>(b.v());
          _stack.emplace_back(_After_BNode{a0.get(), *a1, *a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else if (std::holds_alternative<_After_BNode>(_frame)) {
        auto _f = std::move(std::get<_After_BNode>(_frame));
        _stack.emplace_back(_Combine_BNode{std::move(_result), std::move(_f.a1),
                                           std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_BNode>(_frame));
        _result = f0(_f.a0, std::move(_result), _f.a1, std::move(_f._result));
      }
    }
    return _result;
  }

  /// or_search p t searches tree with || recursion.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static bool
  or_search(F0 &&p,
            const btree &t) { /// _Enter: captures varying parameters for each
                              /// recursive call.

    struct _Enter {
      const btree *t;
    };

    /// _After_BNode: saves [a0], dispatches next recursive call.
    struct _After_BNode {
      const btree *a0;
    };

    /// _Combine_BNode: receives partial results, combines with _result from
    /// final call.
    struct _Combine_BNode {
      bool _result;
    };

    using _Frame = std::variant<_Enter, _After_BNode, _Combine_BNode>;
    bool _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t});
    /// Loopified or_search: _Enter -> _After_BNode -> _Combine_BNode.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const btree &t = *_f.t;
        if (std::holds_alternative<typename btree::BLeaf>(t.v())) {
          const auto &[a0] = std::get<typename btree::BLeaf>(t.v());
          _result = p(a0);
        } else {
          const auto &[a0, a1] = std::get<typename btree::BNode>(t.v());
          _stack.emplace_back(_After_BNode{a0.get()});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else if (std::holds_alternative<_After_BNode>(_frame)) {
        auto _f = std::move(std::get<_After_BNode>(_frame));
        _stack.emplace_back(_Combine_BNode{_result});
        _stack.emplace_back(_Enter{_f.a0});
      } else {
        auto _f = std::move(std::get<_Combine_BNode>(_frame));
        _result = (std::move(_result) || std::move(_f._result));
      }
    }
    return _result;
  }

  /// find_indices p l finds all indices where predicate holds.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t> find_indices_aux(F0 &&p, const List<uint64_t> &l,
                                         uint64_t idx) {
    std::unique_ptr<List<uint64_t>> _head{};
    std::unique_ptr<List<uint64_t>> *_write = &_head;
    uint64_t _loop_idx = std::move(idx);
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_unique<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell = std::make_unique<List<uint64_t>>(
              typename List<uint64_t>::Cons(_loop_idx, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_idx = (_loop_idx + 1);
          _loop_l = a1.get();
          continue;
        } else {
          _loop_idx = (_loop_idx + 1);
          _loop_l = a1.get();
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t> find_indices(F0 &&p, const List<uint64_t> &l) {
    return find_indices_aux(p, l, UINT64_C(0));
  }
};

#endif // INCLUDED_LOOPIFY_SEARCH
