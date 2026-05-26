#ifndef INCLUDED_MEM_SAFETY_PROBE16
#define INCLUDED_MEM_SAFETY_PROBE16

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe16 {
  /// Probe 16: Focused on finding RUNTIME memory safety bugs.
  ///
  /// Attack vectors:
  /// 1. Higher-order functions that STORE closures in data structures
  /// then invoke them after the original scope ends
  /// 2. Partial application chains where each link captures a value
  /// that may have been moved
  /// 3. Functions that return closures from match branches where
  /// the closure captures match bindings from an OWNED match
  /// 4. fold/map patterns that build closure lists
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      std::shared_ptr<tree> a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(_v) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, uint64_t a1, tree a2) {
      return tree(Node{std::make_shared<tree>(std::move(a0)), a1,
                       std::make_shared<tree>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// TEST 8: Higher-order map: apply a function to each element
    /// of a tree, building a new tree of closures.
    tree tree_map_val() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return tree::leaf();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return tree::node(a0->tree_map_val(), (a1 + UINT64_C(1)),
                          a2->tree_map_val());
      }
    }

    /// TEST 6: Non-recursive closure from a deeply nested match.
    uint64_t deep_nested_closure(uint64_t n) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return n;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return ((a1 + a2->tree_sum()) + n);
        } else {
          const auto &[a00, a10, a20] = std::get<typename tree::Node>(_sv0.v());
          auto &&_sv1 = *a2;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            return ((((a00->tree_sum() + a10) + a20->tree_sum()) + a1) + n);
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename tree::Node>(_sv1.v());
            return (((((((a00->tree_sum() + a10) + a20->tree_sum()) + a1) +
                       a01->tree_sum()) +
                      a11) +
                     a21->tree_sum()) +
                    n);
          }
        }
      }
    }

    /// TEST 5: A function that takes TWO trees and returns a closure
    /// capturing both. Tests double ownership.
    uint64_t pair_closure(const tree &t2, uint64_t n) const {
      return ((this->tree_sum() + t2.tree_sum()) + n);
    }

    /// TEST 1: Store a closure derived from a tree in a list,
    /// then invoke it after the tree goes out of scope.
    /// The closure should capture by value.
    uint64_t make_summer(uint64_t n) const { return (this->tree_sum() + n); }

    uint64_t tree_sum() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return ((a0->tree_sum() + a1) + a2->tree_sum());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return f0(*a0, a0->template tree_rec<T1>(f, f0), a1, *a2,
                  a2->template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return f0(*a0, a0->template tree_rect<T1>(f, f0), a1, *a2,
                  a2->template tree_rect<T1>(f, f0));
      }
    }
  };

  template <typename A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      A a0;
      std::shared_ptr<mylist<A>> a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : v_(_v) {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->v_ = Mynil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->v_ = Mycons{
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (a0.type() == typeid(A))
                  return std::any_cast<A>(a0);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(a0);
                  return A{
                      [&]() -> typename A::first_type {
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
                return std::any_cast<A>(a0);
              } else
                return A(a0);
            }(),
            a1 ? std::make_shared<mylist<A>>(*a1) : nullptr};
      }
    }

    static mylist<A> mynil() { return mylist(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t length() const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return (UINT64_C(1) + a1->length());
      }
    }

    mylist<A> myapp(mylist<A> l2) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return l2;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return mylist<A>::mycons(a0, a1->myapp(std::move(l2)));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return f0(a0, *a1, a1->template mylist_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return f0(a0, *a1, a1->template mylist_rect<T1>(f, f0));
      }
    }
  };

  static uint64_t sum_list(const mylist<uint64_t> &l);
  static mylist<std::function<uint64_t(uint64_t)>>
  build_summers(const mylist<tree> &trees);
  static uint64_t
  apply_fns(const mylist<std::function<uint64_t(uint64_t)>> &fns, uint64_t x);
  static inline const uint64_t test_store_closures = []() {
    mylist<tree> trees = mylist<tree>::mycons(
        tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
        mylist<tree>::mycons(
            tree::node(tree::leaf(), UINT64_C(20), tree::leaf()),
            mylist<tree>::mycons(
                tree::node(tree::leaf(), UINT64_C(30), tree::leaf()),
                mylist<tree>::mynil())));
    mylist<std::function<uint64_t(uint64_t)>> fns =
        build_summers(std::move(trees));
    return apply_fns(std::move(fns), UINT64_C(0));
  }();

  /// TEST 2: Fold that accumulates a function by composing closures.
  /// Each step captures the tree from the current list element.
  static uint64_t
  compose_summers(const mylist<tree> &trees,
                  std::function<uint64_t(uint64_t)> acc,
                  uint64_t _x0) { /// _Enter: captures varying parameters for
                                  /// each recursive call.

    struct _Enter {
      std::function<uint64_t(uint64_t)> acc;
      mylist<tree> trees;
    };

    using _Frame = std::variant<_Enter>;
    uint64_t _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{std::move(acc), trees});
    /// Loopified compose_summers: _Enter.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<_Enter>(_frame));
      std::function<uint64_t(uint64_t)> acc = std::move(_f.acc);
      const mylist<tree> &trees = _f.trees;
      _result = [=]() mutable -> std::function<uint64_t(uint64_t)> {
        if (std::holds_alternative<typename mylist<tree>::Mynil>(trees.v())) {
          return acc;
        } else {
          const auto &[a0, a1] =
              std::get<typename mylist<tree>::Mycons>(trees.v());
          const mylist<tree> &a1_value = *a1;
          return [=](uint64_t _x0) mutable -> uint64_t {
            return compose_summers(
                a1_value,
                [=](uint64_t n) mutable { return acc((a0.tree_sum() + n)); },
                _x0);
          };
        }
      }()(_x0);
    }
    return _result;
  }

  static inline const uint64_t test_compose = []() {
    mylist<tree> trees = mylist<tree>::mycons(
        tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
        mylist<tree>::mycons(
            tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
            mylist<tree>::mycons(
                tree::node(tree::leaf(), UINT64_C(15), tree::leaf()),
                mylist<tree>::mynil())));
    return compose_summers(
        std::move(trees), [](uint64_t n) { return n; }, UINT64_C(0));
  }();
  /// TEST 3: Build a list of closures where each closure captures
  /// the SAME tree at different levels.
  /// Tests whether the tree is properly cloned for each closure.
  static mylist<std::function<uint64_t(uint64_t)>>
  multi_capture_tree(tree t, uint64_t n);
  static inline const uint64_t test_multi_capture = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                        UINT64_C(7),
                        tree::node(tree::leaf(), UINT64_C(11), tree::leaf()));
    mylist<std::function<uint64_t(uint64_t)>> fns =
        multi_capture_tree(std::move(t), UINT64_C(3));
    return apply_fns(std::move(fns), UINT64_C(0));
  }();
  /// TEST 4: Return a closure from inside a NESTED match.
  /// The closure captures bindings from BOTH match levels.
  static uint64_t nested_match_closure(const tree &t, const mylist<uint64_t> &l,
                                       uint64_t n);
  static inline const uint64_t test_nested_match = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                        UINT64_C(10),
                        tree::node(tree::leaf(), UINT64_C(15), tree::leaf()));
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(7),
        mylist<uint64_t>::mycons(UINT64_C(99), mylist<uint64_t>::mynil()));
    return nested_match_closure(std::move(t), std::move(l), UINT64_C(3));
  }();
  static inline const uint64_t test_pair_closure = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), UINT64_C(100), tree::leaf());
      tree t2 = tree::node(tree::node(tree::leaf(), UINT64_C(50), tree::leaf()),
                           UINT64_C(25), tree::leaf());
      std::function<uint64_t(uint64_t)> f =
          [=](uint64_t _x0) mutable -> uint64_t {
        return t1.pair_closure(t2, _x0);
      };
      return (f(UINT64_C(0)) + f(UINT64_C(0)));
    }();
  }();
  static inline const uint64_t test_deep_nested = []() {
    tree t = tree::node(
        tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                   UINT64_C(2),
                   tree::node(tree::leaf(), UINT64_C(3), tree::leaf())),
        UINT64_C(10),
        tree::node(tree::node(tree::leaf(), UINT64_C(4), tree::leaf()),
                   UINT64_C(5),
                   tree::node(tree::leaf(), UINT64_C(6), tree::leaf())));
    return std::move(t).deep_nested_closure(UINT64_C(0));
  }();
  /// TEST 7: Map + apply pattern: build closures from tree children,
  /// apply them to values from another list.
  static mylist<uint64_t>
  zip_apply(const mylist<std::function<uint64_t(uint64_t)>> &fns,
            const mylist<uint64_t> &vals);
  static inline const uint64_t test_zip_apply = []() {
    mylist<tree> trees = mylist<tree>::mycons(
        tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
        mylist<tree>::mycons(
            tree::node(tree::leaf(), UINT64_C(20), tree::leaf()),
            mylist<tree>::mynil()));
    mylist<std::function<uint64_t(uint64_t)>> fns =
        build_summers(std::move(trees));
    mylist<uint64_t> vals = mylist<uint64_t>::mycons(
        UINT64_C(1),
        mylist<uint64_t>::mycons(UINT64_C(2), mylist<uint64_t>::mynil()));
    mylist<uint64_t> results = zip_apply(std::move(fns), std::move(vals));
    return sum_list(std::move(results));
  }();
  static inline const uint64_t test_tree_map = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                        UINT64_C(2),
                        tree::node(tree::leaf(), UINT64_C(3), tree::leaf()));
    return std::move(t).tree_map_val().tree_sum();
  }();

  /// TEST 9: CPS-style flattening where each step builds a continuation
  /// that captures tree structure.
  static mylist<uint64_t> flatten_cps_aux(
      const tree &t,
      std::function<mylist<uint64_t>(mylist<uint64_t>)>
          k) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      std::function<mylist<uint64_t>(mylist<uint64_t>)> k;
      const tree *t;
    };

    using _Frame = std::variant<_Enter>;
    mylist<uint64_t> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{std::move(k), &t});
    /// Loopified flatten_cps_aux: _Enter.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<_Enter>(_frame));
      std::function<mylist<uint64_t>(mylist<uint64_t>)> k = std::move(_f.k);
      const tree &t = *_f.t;
      if (std::holds_alternative<typename tree::Leaf>(t.v())) {
        _result = k(mylist<uint64_t>::mynil());
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        _stack.emplace_back(
            _Enter{[=](const mylist<uint64_t> &ll) mutable {
                     return flatten_cps_aux(
                         a2_value, [=](mylist<uint64_t> rl) mutable {
                           return k(ll.myapp(mylist<uint64_t>::mycons(a1, rl)));
                         });
                   },
                   a0.get()});
      }
    }
    return _result;
  }

  static mylist<uint64_t> flatten_cps(const tree &t);
  static inline const uint64_t test_flatten_cps = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                        UINT64_C(2),
                        tree::node(tree::leaf(), UINT64_C(3), tree::leaf()));
    return sum_list(flatten_cps(std::move(t)));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE16
