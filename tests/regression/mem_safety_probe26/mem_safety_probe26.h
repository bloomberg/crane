#ifndef INCLUDED_MEM_SAFETY_PROBE26
#define INCLUDED_MEM_SAFETY_PROBE26

#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

struct MemSafetyProbe26 {
  /// Probe 26: Closures stored in inductives capturing match-bound tree data.
  ///
  /// Attack vector: Force creation of actual closure objects (not inlined)
  /// by storing them in inductive constructors. The closures capture
  /// tree children from match bindings, which are structured binding
  /// references to unique_ptr fields. If Crane fails to create explicit
  /// value copies, the closures hold dangling references.
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

    /// TEST 8: Conditional closure creation — match result determines
    /// which closure to store. Both branches create closures that
    /// capture tree data.
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
    conditional_closure(uint64_t n) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair([](uint64_t x) { return x; }, UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        if (n <= a1) {
          return std::make_pair(
              [=](uint64_t x) mutable { return (x + a0_value.tree_sum()); },
              a1);
        } else {
          return std::make_pair(
              [=](uint64_t x) mutable { return (x + a2_value.tree_sum()); },
              a1);
        }
      }
    }

    /// TEST 7: Closure captures tree child and also uses it immediately
    /// in an expression — tests clone independence under shared access.
    std::pair<std::function<uint64_t(uint64_t)>, tree>
    shared_child_closure() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair([](uint64_t x) { return x; }, tree::leaf());
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        return std::make_pair(
            [=](uint64_t x) mutable { return (x + a0_value.tree_sum()); },
            a0_value);
      }
    }

    /// TEST 6: Closure captures grandchild — two levels of deref.
    /// ll is accessed via l which is accessed via t.
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
    deep_closure_pair() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair([](uint64_t x) { return x; }, UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        if (std::holds_alternative<typename tree::Leaf>(a0_value.v())) {
          return std::make_pair([=](uint64_t x) mutable { return (x + a1); },
                                UINT64_C(0));
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename tree::Node>(a0_value.v());
          const tree &a00_value = *a00;
          const tree &a20_value = *a20;
          return std::make_pair(
              [=](uint64_t x) mutable {
                return ((x + a00_value.tree_sum()) + a10);
              },
              (a1 + a20_value.tree_sum()));
        }
      }
    }

    /// TEST 5: Closure captures tree child, then child is also used
    /// elsewhere in the same expression. Tests whether clone is
    /// independent of the original.
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
    closure_and_sum() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair([](uint64_t x) { return x; }, UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        return std::make_pair(
            [=](uint64_t x) mutable { return (x + a0_value.tree_sum()); },
            ((a0_value.tree_sum() + a1) + a2_value.tree_sum()));
      }
    }

    /// TEST 3: Closure stored in option, captures tree children.
    /// The option prevents inlining.
    std::optional<std::function<uint64_t(uint64_t)>> match_to_option() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::optional<std::function<uint64_t(uint64_t)>>();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        return std::make_optional<std::function<uint64_t(uint64_t)>>(
            [=](uint64_t x) mutable {
              return (((x + a0_value.tree_sum()) + a1) + a2_value.tree_sum());
            });
      }
    }

    /// TEST 2: Two closures in a pair, each captures a different child.
    /// Tests that both children are correctly cloned into their
    /// respective closures.
    std::pair<std::function<uint64_t(uint64_t)>,
              std::function<uint64_t(uint64_t)>>
    split_closures() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair([](uint64_t x) { return x; },
                              [](uint64_t x) { return x; });
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        return std::make_pair(
            [=](uint64_t x) mutable {
              return ((x + a0_value.tree_sum()) + a1);
            },
            [=](uint64_t x) mutable {
              return ((x + a1) + a2_value.tree_sum());
            });
      }
    }

    /// TEST 1: Closure stored in pair, captures tree children from match.
    /// The closure captures l and r — tree children accessed via unique_ptr.
    /// The test constructs the pair, then calls the closure after the
    /// original tree temporary is destroyed.
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
    match_to_pair() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair([](uint64_t x) { return x; }, UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        return std::make_pair(
            [=](uint64_t x) mutable {
              return ((x + a0_value.tree_sum()) + a2_value.tree_sum());
            },
            a1);
      }
    }

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

  static inline const uint64_t test_match_to_pair = []() {
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t> p =
        tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                   UINT64_C(7),
                   tree::node(tree::leaf(), UINT64_C(11), tree::leaf()))
            .match_to_pair();
    return (p.first(UINT64_C(100)) + p.second);
  }();
  static inline const uint64_t test_split_closures = []() {
    std::pair<std::function<uint64_t(uint64_t)>,
              std::function<uint64_t(uint64_t)>>
        p = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                       UINT64_C(7),
                       tree::node(tree::leaf(), UINT64_C(11), tree::leaf()))
                .split_closures();
    return (p.first(UINT64_C(100)) + p.second(UINT64_C(200)));
  }();
  static inline const uint64_t test_match_to_option = []() -> uint64_t {
    auto _cs = tree::node(tree::node(tree::leaf(), UINT64_C(2), tree::leaf()),
                          UINT64_C(5),
                          tree::node(tree::leaf(), UINT64_C(8), tree::leaf()))
                   .match_to_option();
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(100));
    } else {
      return UINT64_C(0);
    }
  }();

  /// TEST 4: Recursive function building list of closures.
  /// Each closure captures tree children from its level.
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

  static mylist<std::function<uint64_t(uint64_t)>>
  build_tree_closures(const tree &t);
  static uint64_t
  apply_first_closure(const mylist<std::function<uint64_t(uint64_t)>> &l,
                      uint64_t x);
  static inline const uint64_t test_build_tree_closures = []() {
    mylist<std::function<uint64_t(uint64_t)>> closures =
        build_tree_closures(tree::node(
            tree::node(tree::leaf(), UINT64_C(4), tree::leaf()), UINT64_C(6),
            tree::node(tree::leaf(), UINT64_C(9), tree::leaf())));
    return apply_first_closure(std::move(closures), UINT64_C(100));
  }();
  static inline const uint64_t test_closure_and_sum = []() {
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t> p =
        tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                   UINT64_C(7),
                   tree::node(tree::leaf(), UINT64_C(11), tree::leaf()))
            .closure_and_sum();
    return (p.first(UINT64_C(100)) + p.second);
  }();
  static inline const uint64_t test_deep_closure_pair = []() {
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t> p =
        tree::node(
            tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                       UINT64_C(2),
                       tree::node(tree::leaf(), UINT64_C(3), tree::leaf())),
            UINT64_C(10), tree::leaf())
            .deep_closure_pair();
    return (p.first(UINT64_C(100)) + p.second);
  }();
  static inline const uint64_t test_shared_child_closure = []() {
    std::pair<std::function<uint64_t(uint64_t)>, tree> p =
        tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                   UINT64_C(10), tree::leaf())
            .shared_child_closure();
    return (p.first(UINT64_C(100)) + p.second.tree_sum());
  }();
  static inline const uint64_t test_conditional_closure = []() {
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t> p1 =
        tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                   UINT64_C(7),
                   tree::node(tree::leaf(), UINT64_C(11), tree::leaf()))
            .conditional_closure(UINT64_C(5));
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t> p2 =
        tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                   UINT64_C(7),
                   tree::node(tree::leaf(), UINT64_C(11), tree::leaf()))
            .conditional_closure(UINT64_C(10));
    return (((p1.first(UINT64_C(100)) + p1.second) + p2.first(UINT64_C(200))) +
            p2.second);
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE26
