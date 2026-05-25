#ifndef INCLUDED_MEM_SAFETY_PROBE15
#define INCLUDED_MEM_SAFETY_PROBE15

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe15 {
  /// Probe 15: Focused on finding RUNTIME memory safety bugs.
  ///
  /// Key attack vectors:
  /// 1. Flatten optimization: v_mut() + unique_ptr field moves
  /// in loopified Enter frames
  /// 2. Value-type tree where subtrees are read AFTER being
  /// potentially moved by the frame push
  /// 3. Closures that capture match bindings from owned matches
  /// 4. Deep trees with many unique_ptr indirections
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

    /// TEST 7: Two passes over the same tree.
    /// First pass collects values, second pass computes sums.
    /// Tests that the tree is not consumed by the first pass.
    uint64_t two_pass() const {
      mylist<uint64_t> vals = flatten(*this);
      mylist<uint64_t> sums = subtree_sums(*this);
      return (sum_list(std::move(vals)) + sum_list(std::move(sums)));
    }

    /// TEST 4: Tree zipping — combine two trees into one.
    tree zip_trees(tree t2) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return t2;
      } else {
        auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        if (std::holds_alternative<typename tree::Leaf>(t2.v_mut())) {
          return *this;
        } else {
          auto &[a00, a10, a20] = std::get<typename tree::Node>(t2.v_mut());
          return tree::node(a0->zip_trees(*a00),
                            (std::move(a1) + std::move(a10)),
                            a2->zip_trees(*a20));
        }
      }
    }

    /// TEST 3: Tree mirror that uses both subtrees.
    tree mirror() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return tree::leaf();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return tree::node(a2->mirror(), a1, a0->mirror());
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

    /// TEST 8: Map over a list, transforming each element.
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

    /// TEST 6: List reversal using accumulator.
    /// Tests owned parameter match optimization.
    mylist<A> rev_aux(mylist<A> acc) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return acc;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return a1->rev_aux(mylist<A>::mycons(a0, std::move(acc)));
      }
    }

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
  /// TEST 1: Tree flattening where left subtree is used AFTER
  /// right subtree recursive call.
  /// In loopified code, the Enter frame for the right subtree
  /// may move the left subtree's pointer.
  static mylist<uint64_t> flatten(const tree &t);
  static inline const uint64_t test_flatten = []() {
    tree t = tree::node(
        tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                   UINT64_C(2),
                   tree::node(tree::leaf(), UINT64_C(3), tree::leaf())),
        UINT64_C(4),
        tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                   UINT64_C(6),
                   tree::node(tree::leaf(), UINT64_C(7), tree::leaf())));
    return sum_list(flatten(std::move(t)));
  }();
  /// TEST 2: Tree to list where each element is the sum of
  /// its subtree. Uses both subtrees for computation AND recursion.
  static mylist<uint64_t> subtree_sums(const tree &t);
  static inline const uint64_t test_subtree_sums = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                        UINT64_C(7),
                        tree::node(tree::leaf(), UINT64_C(11), tree::leaf()));
    return sum_list(subtree_sums(std::move(t)));
  }();
  static inline const uint64_t test_mirror = []() {
    tree t = tree::node(
        tree::node(tree::leaf(), UINT64_C(1),
                   tree::node(tree::leaf(), UINT64_C(2), tree::leaf())),
        UINT64_C(3), tree::node(tree::leaf(), UINT64_C(4), tree::leaf()));
    return std::move(t).mirror().tree_sum();
  }();
  static inline const uint64_t test_zip = []() {
    tree t1 = tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                         UINT64_C(10),
                         tree::node(tree::leaf(), UINT64_C(2), tree::leaf()));
    tree t2 = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                         UINT64_C(20),
                         tree::node(tree::leaf(), UINT64_C(4), tree::leaf()));
    return std::move(t1).zip_trees(std::move(t2)).tree_sum();
  }();
  /// TEST 5: Deep left-spine tree.
  /// Stresses the frame stack depth.
  static tree left_spine(uint64_t n);
  static inline const uint64_t test_deep_spine =
      left_spine(UINT64_C(100)).tree_sum();
  static inline const uint64_t test_rev = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(1),
        mylist<uint64_t>::mycons(
            UINT64_C(2),
            mylist<uint64_t>::mycons(
                UINT64_C(3), mylist<uint64_t>::mycons(
                                 UINT64_C(4), mylist<uint64_t>::mynil()))));
    mylist<uint64_t> r = std::move(l).rev_aux(mylist<uint64_t>::mynil());
    return sum_list(std::move(r));
  }();
  static inline const uint64_t test_two_pass =
      tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                 UINT64_C(7),
                 tree::node(tree::leaf(), UINT64_C(11), tree::leaf()))
          .two_pass();
  static inline const uint64_t test_map = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(10),
        mylist<uint64_t>::mycons(
            UINT64_C(20),
            mylist<uint64_t>::mycons(UINT64_C(30), mylist<uint64_t>::mynil())));
    mylist<uint64_t> l2 = std::move(l).template map_list<uint64_t>(
        [](uint64_t x) { return (x + UINT64_C(1)); });
    return sum_list(std::move(l2));
  }();
  /// TEST 9: Build a large tree and verify all values are preserved.
  static tree make_tree(uint64_t n);
  static inline const uint64_t test_large_tree =
      make_tree(UINT64_C(6)).tree_sum();
};

#endif // INCLUDED_MEM_SAFETY_PROBE15
