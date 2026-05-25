#ifndef INCLUDED_MEM_SAFETY_PROBE18
#define INCLUDED_MEM_SAFETY_PROBE18

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe18 {
  /// Probe 18: Complex ownership handoff patterns.
  ///
  /// Attack vectors:
  /// 1. Functions where the SAME argument appears in multiple positions
  /// of a single constructor call (potential double-move)
  /// 2. let-binding a function of a value, then using the value AGAIN
  /// (ownership tracking across let-bindings)
  /// 3. Passing a closure to a higher-order function that calls it
  /// multiple times (std::function copy semantics)
  /// 4. Complex constructor nesting where tree values appear at
  /// multiple levels
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

    /// TEST 9: Triple-use of a tree: compute sum, build a new tree, compute sum
    /// again
    uint64_t triple_use() const {
      uint64_t s1 = this->tree_sum();
      tree t2 = tree::node(*this, s1, *this);
      uint64_t s2 = std::move(t2).tree_sum();
      return (s1 + s2);
    }

    /// TEST 7: Use a value type in a chain of let-bindings where
    /// each binding transforms the tree.
    uint64_t chain_transforms() const {
      tree t1 = tree::node(*this, UINT64_C(0), tree::leaf());
      tree t2 = tree::node(tree::leaf(), UINT64_C(0), std::move(t1));
      tree t3 = tree::node(std::move(t2), UINT64_C(0), std::move(*this));
      return std::move(t3).tree_sum();
    }

    /// TEST 4: Build a tree from a tree, using it at multiple levels.
    tree tree_from_tree() const {
      return tree::node(tree::node(*this, UINT64_C(0), tree::leaf()),
                        this->tree_sum(),
                        tree::node(tree::leaf(), UINT64_C(0), *this));
    }

    /// TEST 2: Let-bind tree_sum, then use the tree again.
    /// The tree should NOT be consumed by tree_sum.
    uint64_t let_reuse() const {
      uint64_t s = this->tree_sum();
      return (s + this->tree_sum());
    }

    /// TEST 1: Same tree used in TWO different positions of a single
    /// constructor. Tests whether the tree is properly cloned.
    tree dup_tree() const { return tree::node(*this, UINT64_C(0), *this); }

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

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    mylist<T1> map_list(F0 &&f) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return mylist<T1>::mynil();
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return mylist<T1>::mycons(f(a0), a1->template map_list<T1>(f));
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
  static inline const uint64_t test_dup = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(42), tree::leaf());
    return std::move(t).dup_tree().tree_sum();
  }();
  static inline const uint64_t test_let_reuse =
      tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                 UINT64_C(10),
                 tree::node(tree::leaf(), UINT64_C(15), tree::leaf()))
          .let_reuse();

  /// TEST 3: Apply a higher-order function multiple times
  /// to a closure that captures a tree.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t apply_twice(F0 &&f, uint64_t x) {
    return f(f(x));
  }

  static inline const uint64_t test_apply_twice = []() {
    return []() {
      tree t = tree::node(tree::leaf(), UINT64_C(7), tree::leaf());
      std::function<uint64_t(uint64_t)> f = [=](uint64_t n) mutable {
        return (t.tree_sum() + n);
      };
      return apply_twice(f, UINT64_C(0));
    }();
  }();
  static inline const uint64_t test_tree_from_tree = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(5), tree::leaf());
    return std::move(t).tree_from_tree().tree_sum();
  }();
  /// TEST 5: Complex fold that builds a tree from a list.
  static tree fold_left_tree(const mylist<uint64_t> &l, tree acc);
  static inline const uint64_t test_fold_tree = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(1),
        mylist<uint64_t>::mycons(
            UINT64_C(2),
            mylist<uint64_t>::mycons(UINT64_C(3), mylist<uint64_t>::mynil())));
    return fold_left_tree(std::move(l), tree::leaf()).tree_sum();
  }(); /// TEST 6: Concat two lists, using both in the result.

  template <typename T1>
  static mylist<T1> concat_flat(
      const mylist<mylist<T1>> &
          ls) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const mylist<mylist<T1>> *ls;
    };

    /// _Resume_Mycons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Mycons {
      mylist<T1> a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Mycons>;
    mylist<T1> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&ls});
    /// Loopified concat_flat: _Enter -> _Resume_Mycons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const mylist<mylist<T1>> &ls = *_f.ls;
        if (std::holds_alternative<typename mylist<mylist<T1>>::Mynil>(
                ls.v())) {
          _result = mylist<T1>::mynil();
        } else {
          const auto &[a0, a1] =
              std::get<typename mylist<mylist<T1>>::Mycons>(ls.v());
          _stack.emplace_back(_Resume_Mycons{a0});
          _stack.emplace_back(_Enter{a1.get()});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Mycons>(_frame));
        _result = _f.a0.myapp(_result);
      }
    }
    return _result;
  }

  static inline const uint64_t test_concat = []() {
    mylist<uint64_t> l1 = mylist<uint64_t>::mycons(
        UINT64_C(1),
        mylist<uint64_t>::mycons(UINT64_C(2), mylist<uint64_t>::mynil()));
    mylist<uint64_t> l2 = mylist<uint64_t>::mycons(
        UINT64_C(3),
        mylist<uint64_t>::mycons(UINT64_C(4), mylist<uint64_t>::mynil()));
    mylist<uint64_t> l3 = mylist<uint64_t>::mycons(
        UINT64_C(5),
        mylist<uint64_t>::mycons(UINT64_C(6), mylist<uint64_t>::mynil()));
    mylist<mylist<uint64_t>> ls = mylist<mylist<uint64_t>>::mycons(
        std::move(l1),
        mylist<mylist<uint64_t>>::mycons(
            std::move(l2),
            mylist<mylist<uint64_t>>::mycons(
                std::move(l3), mylist<mylist<uint64_t>>::mynil())));
    return sum_list(concat_flat<uint64_t>(std::move(ls)));
  }();
  static inline const uint64_t test_chain = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    return std::move(t).chain_transforms();
  }();
  /// TEST 8: Nested constructor building: build a list of trees
  /// using the same tree in different positions.
  static mylist<tree> build_tree_list(tree t, uint64_t n);
  static uint64_t sum_tree_list(const mylist<tree> &l);
  static inline const uint64_t test_build_tree_list = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    mylist<tree> trees = build_tree_list(std::move(t), UINT64_C(3));
    return sum_tree_list(std::move(trees));
  }();
  static inline const uint64_t test_triple_use =
      tree::node(tree::leaf(), UINT64_C(7), tree::leaf()).triple_use();
};

#endif // INCLUDED_MEM_SAFETY_PROBE18
