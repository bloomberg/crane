#ifndef INCLUDED_LOOPIFY_SEARCH
#define INCLUDED_LOOPIFY_SEARCH

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
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

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List *_loop_self = this;
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

struct LoopifySearch {
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
    crane::small_vector<_Frame> _stack;
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
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }

  static uint64_t
  knapsack_fuel(uint64_t fuel, uint64_t capacity,
                const List<std::pair<uint64_t, uint64_t>> &items);
  static uint64_t knapsack(uint64_t capacity,
                           const List<std::pair<uint64_t, uint64_t>> &items);
  static std::pair<uint64_t, uint64_t> majority(const List<uint64_t> &l);
  static List<uint64_t> longest_increasing_subseq(const List<uint64_t> &l);

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &, uint64_t &>
  static uint64_t
  maximum_by(F0 &&cmp,
             const List<uint64_t> &l) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const List<uint64_t> *l;
    };

    /// _Cont_Cons: saves [a0], resumes after recursive call, then processes
    /// rest.
    struct _Cont_Cons {
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Cont_Cons>;
    uint64_t _result{};
    crane::small_vector<_Frame> _stack;
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
            _stack.emplace_back(_Cont_Cons{a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        }
      } else {
        auto _f = std::move(std::get<_Cont_Cons>(_frame));
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

  static uint64_t nth_impl(uint64_t n, const List<uint64_t> &l);
  static List<uint64_t> take_impl(uint64_t k, const List<uint64_t> &l);
  static List<uint64_t> drop_impl(uint64_t k, List<uint64_t> l);
  static bool binary_search_fuel(uint64_t fuel, uint64_t target,
                                 const List<uint64_t> &l);
  static bool binary_search(uint64_t target, const List<uint64_t> &l);
  static List<uint64_t> longest_run_aux(List<uint64_t> current_run,
                                        List<uint64_t> best_run,
                                        const List<uint64_t> &l);
  static List<uint64_t> longest_run(const List<uint64_t> &l);
  static uint64_t collatz_fuel(uint64_t fuel, uint64_t n);
  static uint64_t collatz(uint64_t n);
  static List<uint64_t> lis(const List<uint64_t> &l);
  static bool subset_sum_fuel(uint64_t fuel, uint64_t target,
                              const List<uint64_t> &l);
  static bool subset_sum(uint64_t target, const List<uint64_t> &l);

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

  static List<uint64_t> sieve_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> sieve(const List<uint64_t> &l);
  static bool elem_impl(uint64_t x, const List<uint64_t> &l);
  static List<uint64_t> nub_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> nub(const List<uint64_t> &l);
  static List<uint64_t> remove_duplicates_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> remove_duplicates(const List<uint64_t> &l);
  static List<uint64_t> quicksort_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> quicksort(const List<uint64_t> &l);
  static std::pair<List<uint64_t>, List<uint64_t>>
  split_list(const List<uint64_t> &l);
  static List<uint64_t> merge_sorted_fuel(uint64_t fuel, List<uint64_t> l1,
                                          List<uint64_t> l2);
  static List<uint64_t> merge_sorted(const List<uint64_t> &l1,
                                     const List<uint64_t> &l2);
  static List<uint64_t> merge_sort_fuel(uint64_t fuel, List<uint64_t> l);
  static List<uint64_t> merge_sort(const List<uint64_t> &l);
  static List<uint64_t> remove_first(uint64_t x, const List<uint64_t> &l);

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
    crane::small_vector<_Frame> _stack;
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
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = std::move(_f.a0).app(std::move(_result));
      }
    }
    return _result;
  }

  static List<List<uint64_t>> map_cons(uint64_t x,
                                       const List<List<uint64_t>> &lsts);
  static List<List<uint64_t>> perms_choices_fuel(uint64_t fuel,
                                                 const List<uint64_t> &choices,
                                                 const List<uint64_t> &orig);
  static List<List<uint64_t>> permutations_fuel(uint64_t fuel,
                                                const List<uint64_t> &l);
  static List<List<uint64_t>> permutations(const List<uint64_t> &l);
  static std::optional<uint64_t>
  linear_search_aux(uint64_t x, const List<uint64_t> &l, uint64_t idx);
  static std::optional<uint64_t> linear_search(uint64_t x,
                                               const List<uint64_t> &l);
  static List<uint64_t> all_indices_aux(uint64_t x, const List<uint64_t> &l,
                                        uint64_t idx);
  static List<uint64_t> all_indices(uint64_t x, const List<uint64_t> &l);
  static uint64_t min_element(const List<uint64_t> &l);

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
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
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
    btree(btree &&) noexcept = default;
    btree &operator=(btree &&) noexcept = default;

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
      std::decay_t<T1> _result;
      btree a1;
      btree a0;
    };

    using _Frame = std::variant<_Enter, _After_BNode, _Combine_BNode>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
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
          _stack.emplace_back(_After_BNode{crane_raw(a0), *a1, *a0});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else if (std::holds_alternative<_After_BNode>(_frame)) {
        auto _f = std::move(std::get<_After_BNode>(_frame));
        _stack.emplace_back(_Combine_BNode{std::move(_result), std::move(_f.a1),
                                           std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_BNode>(_frame));
        _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                     std::move(_f._result));
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
      std::decay_t<T1> _result;
      btree a1;
      btree a0;
    };

    using _Frame = std::variant<_Enter, _After_BNode, _Combine_BNode>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
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
          _stack.emplace_back(_After_BNode{crane_raw(a0), *a1, *a0});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else if (std::holds_alternative<_After_BNode>(_frame)) {
        auto _f = std::move(std::get<_After_BNode>(_frame));
        _stack.emplace_back(_Combine_BNode{std::move(_result), std::move(_f.a1),
                                           std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_BNode>(_frame));
        _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                     std::move(_f._result));
      }
    }
    return _result;
  }

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
    crane::small_vector<_Frame> _stack;
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
          _stack.emplace_back(_After_BNode{crane_raw(a0)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else if (std::holds_alternative<_After_BNode>(_frame)) {
        auto _f = std::move(std::get<_After_BNode>(_frame));
        _stack.emplace_back(_Combine_BNode{std::move(_result)});
        _stack.emplace_back(_Enter{_f.a0});
      } else {
        auto _f = std::move(std::get<_Combine_BNode>(_frame));
        _result = (std::move(_result) || std::move(_f._result));
      }
    }
    return _result;
  }

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
