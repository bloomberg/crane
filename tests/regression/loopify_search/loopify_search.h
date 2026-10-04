#ifndef INCLUDED_LOOPIFY_SEARCH
#define INCLUDED_LOOPIFY_SEARCH

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
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
  len_impl(const List<T1> &l) { /// CraneEnter: captures varying parameters for
                                /// each recursive call.

    struct CraneEnter {
      const List<T1> *l;
    };

    /// CraneCont_Cons: resumes after recursive call, then processes rest.
    struct CraneCont_Cons {};

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified len_impl: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<T1> &l = *_f.l;
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        _result = (std::move(_result) + 1);
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
             const List<uint64_t> &l) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

    struct CraneEnter {
      const List<uint64_t> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified maximum_by: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          auto &&_sv = *a1;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
            _result = std::move(a0);
          } else {
            _stack.emplace_back(CraneCont_Cons{a0});
            _stack.emplace_back(CraneEnter{crane_raw(a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        uint64_t m = std::move(_result);
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
  static bool subset_sum(uint64_t target, const List<uint64_t> &l);

  /// Helper: filter predicate.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t> filter_impl(F0 &&p, const List<uint64_t> &l) {
    std::shared_ptr<List<uint64_t>> _head{};
    std::shared_ptr<List<uint64_t>> *_write = &_head;
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell = std::make_shared<List<uint64_t>>(
              typename List<uint64_t>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_l = crane_raw(a1);
          continue;
        } else {
          _loop_l = crane_raw(a1);
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
             const List<uint64_t> &l) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

    struct CraneEnter {
      const List<uint64_t> *l;
    };

    /// CraneCont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_Cons {
      uint64_t a0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    List<List<uint64_t>> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified concat_map: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const List<uint64_t> &l = *_f.l;
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
          _result = List<List<uint64_t>>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        _result = f(a0).app(std::move(_result));
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
      std::shared_ptr<btree> a0;
      std::shared_ptr<btree> a1;
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

    static btree bleaf(uint64_t a0) { return btree(BLeaf{a0}); }

    static btree bnode(btree a0, btree a1) {
      return btree(BNode{std::make_shared<btree>(std::move(a0)),
                         std::make_shared<btree>(std::move(a1))});
    }

    // MANIPULATORS
    ~btree() {
      crane::small_vector<std::shared_ptr<btree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<BNode>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    btree(const btree &) = default;
    btree &operator=(const btree &) = default;
    btree(btree &&) = default;
    btree &operator=(btree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, btree &, T1 &, btree &, T1 &>
  static T1 btree_rect(F0 &&f, F1 &&f0,
                       const btree &b) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

    struct CraneEnter {
      const btree *b;
    };

    /// CraneCont_BNode: saves [a0, a1], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_BNode {
      std::shared_ptr<btree> a0;
      const btree *a1;
    };

    /// CraneCont_BNode_1: saves [_tmp2, a0, a1], resumes after recursive call,
    /// then processes rest.
    struct CraneCont_BNode_1 {
      T1 _tmp2;
      std::shared_ptr<btree> a0;
      const btree *a1;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_BNode, CraneCont_BNode_1>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&b});
    /// Loopified btree_rect: CraneEnter -> CraneCont_BNode ->
    /// CraneCont_BNode_1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const btree &b = *_f.b;
        if (std::holds_alternative<typename btree::BLeaf>(b.v())) {
          const auto &[a0] = std::get<typename btree::BLeaf>(b.v());
          _result = f(a0);
        } else {
          const auto &[a0, a1] = std::get<typename btree::BNode>(b.v());
          _stack.emplace_back(CraneCont_BNode{a0, crane_raw(a1)});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_BNode>(_frame)) {
        auto _f = std::move(std::get<CraneCont_BNode>(_frame));
        std::shared_ptr<btree> a0 = std::move(_f.a0);
        const btree &a1 = *_f.a1;
        _stack.emplace_back(
            CraneCont_BNode_1{std::move(_result), std::move(a0), &a1});
        _stack.emplace_back(CraneEnter{&a1});
      } else {
        auto _f = std::move(std::get<CraneCont_BNode_1>(_frame));
        std::shared_ptr<btree> a0 = std::move(_f.a0);
        const btree &a1 = *_f.a1;
        _result = f0(*a0, std::move(_f._tmp2), a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, btree &, T1 &, btree &, T1 &>
  static T1 btree_rec(F0 &&f, F1 &&f0,
                      const btree &b) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

    struct CraneEnter {
      const btree *b;
    };

    /// CraneCont_BNode: saves [a0, a1], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_BNode {
      std::shared_ptr<btree> a0;
      const btree *a1;
    };

    /// CraneCont_BNode_1: saves [_tmp2, a0, a1], resumes after recursive call,
    /// then processes rest.
    struct CraneCont_BNode_1 {
      T1 _tmp2;
      std::shared_ptr<btree> a0;
      const btree *a1;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_BNode, CraneCont_BNode_1>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&b});
    /// Loopified btree_rec: CraneEnter -> CraneCont_BNode -> CraneCont_BNode_1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const btree &b = *_f.b;
        if (std::holds_alternative<typename btree::BLeaf>(b.v())) {
          const auto &[a0] = std::get<typename btree::BLeaf>(b.v());
          _result = f(a0);
        } else {
          const auto &[a0, a1] = std::get<typename btree::BNode>(b.v());
          _stack.emplace_back(CraneCont_BNode{a0, crane_raw(a1)});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_BNode>(_frame)) {
        auto _f = std::move(std::get<CraneCont_BNode>(_frame));
        std::shared_ptr<btree> a0 = std::move(_f.a0);
        const btree &a1 = *_f.a1;
        _stack.emplace_back(
            CraneCont_BNode_1{std::move(_result), std::move(a0), &a1});
        _stack.emplace_back(CraneEnter{&a1});
      } else {
        auto _f = std::move(std::get<CraneCont_BNode_1>(_frame));
        std::shared_ptr<btree> a0 = std::move(_f.a0);
        const btree &a1 = *_f.a1;
        _result = f0(*a0, std::move(_f._tmp2), a1, std::move(_result));
      }
    }
    return _result;
  }

  /// or_search p t searches tree with || recursion.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static bool
  or_search(F0 &&p, const btree &t) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

    struct CraneEnter {
      const btree *t;
    };

    /// CraneCont_BNode: saves [a1], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_BNode {
      const btree *a1;
    };

    /// CraneCont_BNode_1: saves [_tmp2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_BNode_1 {
      bool _tmp2;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_BNode, CraneCont_BNode_1>;
    bool _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&t});
    /// Loopified or_search: CraneEnter -> CraneCont_BNode -> CraneCont_BNode_1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const btree &t = *_f.t;
        if (std::holds_alternative<typename btree::BLeaf>(t.v())) {
          const auto &[a0] = std::get<typename btree::BLeaf>(t.v());
          _result = p(a0);
        } else {
          const auto &[a0, a1] = std::get<typename btree::BNode>(t.v());
          _stack.emplace_back(CraneCont_BNode{crane_raw(a1)});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_BNode>(_frame)) {
        auto _f = std::move(std::get<CraneCont_BNode>(_frame));
        const btree &a1 = *_f.a1;
        _stack.emplace_back(CraneCont_BNode_1{std::move(_result)});
        _stack.emplace_back(CraneEnter{&a1});
      } else {
        auto _f = std::move(std::get<CraneCont_BNode_1>(_frame));
        _result = (_f._tmp2 || std::move(_result));
      }
    }
    return _result;
  }

  /// find_indices p l finds all indices where predicate holds.
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static List<uint64_t> find_indices_aux(F0 &&p, const List<uint64_t> &l,
                                         uint64_t idx) {
    std::shared_ptr<List<uint64_t>> _head{};
    std::shared_ptr<List<uint64_t>> *_write = &_head;
    uint64_t _loop_idx = std::move(idx);
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
        break;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        if (p(a0)) {
          auto _cell = std::make_shared<List<uint64_t>>(
              typename List<uint64_t>::Cons(_loop_idx, nullptr));
          *_write = std::move(_cell);
          _write =
              &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
          _loop_idx = (_loop_idx + 1);
          _loop_l = crane_raw(a1);
          continue;
        } else {
          _loop_idx = (_loop_idx + 1);
          _loop_l = crane_raw(a1);
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
