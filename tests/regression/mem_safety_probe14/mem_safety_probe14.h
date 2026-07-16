#ifndef INCLUDED_MEM_SAFETY_PROBE14
#define INCLUDED_MEM_SAFETY_PROBE14

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe14 {
  /// Probe 14: Stress-test closure capture safety.
  ///
  /// Focus on patterns where:
  /// 1. A value type is simultaneously used in a closure AND
  /// consumed by another operation in the same expression
  /// 2. Closures that capture value types are stored in
  /// data structures and later invoked
  /// 3. Closures returned from helper functions that take
  /// value-type parameters by value (move semantics)
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
    ~tree() {
      std::vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// TEST 7: Closure stored in PAIR, then extracted and called.
    /// Tests pair construction + closure capture interaction.
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t> fn_and_val() const {
      uint64_t s = this->tree_sum();
      return std::make_pair([=](uint64_t n) mutable { return (s + n); }, s);
    }

    /// TEST 4: Two closures capture same tree. Both should
    /// have independent copies.
    uint64_t two_closures() const {
      tree _self_val = *this;
      std::function<uint64_t(uint64_t)> f1 = [=](uint64_t n) mutable {
        return (_self_val.tree_sum() + n);
      };
      std::function<uint64_t(uint64_t)> f2 = [=](uint64_t n) mutable {
        return (_self_val.tree_sum() * n);
      };
      return (f1(UINT64_C(3)) + f2(UINT64_C(2)));
    }

    uint64_t closure_then_consume() const {
      tree _self_val = *this;
      std::function<uint64_t(uint64_t)> f = [=](uint64_t n) mutable {
        return (_self_val.tree_sum() + n);
      };
      uint64_t v = std::move(*this).consume_tree();
      return (f(UINT64_C(0)) + v);
    }

    /// TEST 3: Tree used in closure, then tree passed to
    /// function that consumes it. The closure must not
    /// share state with the consumed tree.
    uint64_t consume_tree() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return a1;
      }
    }

    /// TEST 2: Tree used in closure AND in a let-binding.
    /// The let-binding forces evaluation before the closure call.
    /// Tests evaluation order safety.
    uint64_t use_tree_twice() const {
      tree _self_val = *this;
      uint64_t ts = this->tree_sum();
      std::function<uint64_t(uint64_t)> f = [=](uint64_t n) mutable {
        return (_self_val.tree_sum() + n);
      };
      return (ts + f(UINT64_C(0)));
    }

    /// TEST 1: make_adder takes a tree by value (move).
    /// The closure captures tree_sum t. After the closure is created,
    /// t is dead in the caller, so Crane might move t.
    /// But the closure must hold a valid copy.
    uint64_t make_adder(uint64_t n) const { return (this->tree_sum() + n); }

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
    ~mylist() {
      std::vector<std::shared_ptr<mylist<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
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
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// TEST 6: List of closures created from tree traversal.
    /// Each closure captures a value from its level. Closures
    /// are evaluated after the full traversal completes.
    mylist<A> mylist_append(mylist<A> l2) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return l2;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return mylist<A>::mycons(a0, a1->mylist_append(std::move(l2)));
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

  static uint64_t sum_fns(const mylist<std::function<uint64_t(uint64_t)>> &l);
  static inline const uint64_t use_make_adder = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    return std::move(t).make_adder(UINT64_C(5));
  }();
  static inline const uint64_t test_use_twice =
      tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                 UINT64_C(10),
                 tree::node(tree::leaf(), UINT64_C(15), tree::leaf()))
          .use_tree_twice();
  static inline const uint64_t test_closure_consume =
      tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                 UINT64_C(10),
                 tree::node(tree::leaf(), UINT64_C(15), tree::leaf()))
          .closure_then_consume();
  static inline const uint64_t test_two_closures =
      tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                 UINT64_C(10),
                 tree::node(tree::leaf(), UINT64_C(15), tree::leaf()))
          .two_closures();
  /// TEST 5: Closure captures tree, tree is pattern-matched
  /// AFTER closure creation. The match destructures the tree.
  /// The closure must still hold the original tree.
  static uint64_t capture_then_match(tree t);
  static inline const uint64_t test_capture_match =
      capture_then_match(tree::node(
          tree::node(tree::leaf(), UINT64_C(5), tree::leaf()), UINT64_C(10),
          tree::node(tree::leaf(), UINT64_C(15), tree::leaf())));
  static mylist<std::function<uint64_t(uint64_t)>>
  tree_level_fns(const tree &t, uint64_t depth);
  static inline const uint64_t test_level_fns = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                        UINT64_C(7),
                        tree::node(tree::leaf(), UINT64_C(11), tree::leaf()));
    return sum_fns(tree_level_fns(std::move(t), UINT64_C(0)));
  }();
  static inline const uint64_t test_fn_and_val = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(100), tree::leaf()),
                        UINT64_C(200),
                        tree::node(tree::leaf(), UINT64_C(300), tree::leaf()));
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t> p =
        std::move(t).fn_and_val();
    return (p.first(UINT64_C(5)) + p.second);
  }();
  /// TEST 8: Large tree stress test. Many closures, deep recursion.
  static tree make_balanced(uint64_t n);
  static mylist<std::function<uint64_t(uint64_t)>>
  collect_closures(const tree &t);

  static inline const uint64_t test_stress = []() {
    tree t = make_balanced(UINT64_C(8));
    return sum_fns(collect_closures(std::move(t)));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE14
