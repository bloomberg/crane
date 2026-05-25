#ifndef INCLUDED_MEM_SAFETY_PROBE24
#define INCLUDED_MEM_SAFETY_PROBE24

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe24 {
  /// Probe 24: Complex value-type interactions.
  ///
  /// Attack vectors:
  /// 1. Use-after-move in pair/constructor arguments: if Crane
  /// generates std::move(t) alongside t.field in the same expression
  /// 2. Rose-tree with list children: complex ownership when
  /// flattening nested value types
  /// 3. Multi-use of owned variable in constructor calls: t used in
  /// both constructor position AND field-access position
  /// 4. Value-type stored in option/pair then accessed through
  /// projection — tests whether projections access moved-from data
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

    /// TEST 6: Store a tree AND its sum in a pair, then transform
    /// both. Tests that clone is independent of original.
    uint64_t clone_and_transform() const {
      std::pair<tree, uint64_t> p = std::make_pair(*this, this->tree_sum());
      tree t2 = p.first;
      uint64_t s = p.second;
      tree t3 =
          std::move(t2).map_tree([=](uint64_t n) mutable { return (n + s); });
      return std::move(t3).tree_sum();
    }

    /// TEST 5: Nested value type — list of trees stored in a tree-like
    /// structure. Tests clone correctness and ownership for nested types.
    template <typename F0>
      requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
    tree map_tree(F0 &&f) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return tree::leaf();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return tree::node(a0->map_tree(f), f(a1), a2->map_tree(f));
      }
    }

    /// TEST 4: Recursive function where result uses BOTH t (for return)
    /// and t's children (through recursive calls) — not loopified because
    /// return type is pair. Tests use-after-move in make_pair.
    std::pair<tree, uint64_t> tag_tree() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair(tree::leaf(), UINT64_C(0));
      } else {
        auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        std::pair<tree, uint64_t> pl = a0->tag_tree();
        std::pair<tree, uint64_t> pr = a2->tag_tree();
        return std::make_pair(*this, ((std::move(a1) + pl.second) + pr.second));
      }
    }

    /// TEST 3: Triple use of t in one expression.
    std::pair<std::pair<tree, tree>, uint64_t> triple_use() const {
      return std::make_pair(std::make_pair(*this, *this), this->tree_sum());
    }

    /// TEST 2: Pair where BOTH elements use t, one as value
    /// and one through a function.
    std::pair<tree, uint64_t> pair_self() const {
      return std::make_pair(*this, this->tree_sum());
    }

    /// TEST 1: Variable used as BOTH whole value AND for field access
    /// in the same constructor. In C++, tree::node(t, tree_sum(t), Leaf)
    /// where t must be cloned and tree_sum accesses t's children.
    tree self_annotate() const {
      return tree::node(*this, this->tree_sum(), tree::leaf());
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

    uint64_t length() const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return (UINT64_C(1) + a1->length());
      }
    }

    mylist<A> app(mylist<A> l2) const {
      if (std::holds_alternative<typename mylist<A>::Mynil>(this->v())) {
        return l2;
      } else {
        const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(this->v());
        return mylist<A>::mycons(a0, a1->app(std::move(l2)));
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
  static inline const uint64_t test_self_annotate =
      tree::node(tree::leaf(), UINT64_C(5), tree::leaf())
          .self_annotate()
          .tree_sum();
  static inline const uint64_t test_pair_self = []() {
    std::pair<tree, uint64_t> p =
        tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                   UINT64_C(7),
                   tree::node(tree::leaf(), UINT64_C(11), tree::leaf()))
            .pair_self();
    return (p.first.tree_sum() + p.second);
  }();
  static inline const uint64_t test_triple_use = []() {
    std::pair<std::pair<tree, tree>, uint64_t> p =
        tree::node(tree::leaf(), UINT64_C(5), tree::leaf()).triple_use();
    return (((p.first).first.tree_sum() + (p.first).second.tree_sum()) +
            p.second);
  }();
  static inline const uint64_t test_tag_tree = []() {
    std::pair<tree, uint64_t> p =
        tree::node(tree::node(tree::leaf(), UINT64_C(2), tree::leaf()),
                   UINT64_C(5),
                   tree::node(tree::leaf(), UINT64_C(8), tree::leaf()))
            .tag_tree();
    return (p.first.tree_sum() + p.second);
  }();
  static mylist<uint64_t> tree_to_list(const tree &t);
  static inline const uint64_t test_nested_ops = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                        UINT64_C(7),
                        tree::node(tree::leaf(), UINT64_C(11), tree::leaf()));
    tree doubled = t.map_tree([](uint64_t n) { return (n * UINT64_C(2)); });
    mylist<uint64_t> flat = tree_to_list(std::move(doubled));
    return (sum_list(std::move(flat)) + std::move(t).tree_sum());
  }();
  static inline const uint64_t test_clone_and_transform =
      tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                 UINT64_C(2),
                 tree::node(tree::leaf(), UINT64_C(3), tree::leaf()))
          .clone_and_transform();
  /// TEST 7: Build a tree from a list, using accumulated state.
  /// Tests interaction between list recursion and tree construction.
  static tree list_to_tree(const mylist<uint64_t> &l, tree acc);
  static inline const uint64_t test_list_to_tree =
      list_to_tree(
          mylist<uint64_t>::mycons(
              UINT64_C(1),
              mylist<uint64_t>::mycons(
                  UINT64_C(2), mylist<uint64_t>::mycons(
                                   UINT64_C(3), mylist<uint64_t>::mynil()))),
          tree::leaf())
          .tree_sum();
  /// TEST 8: Zip two trees, producing a list of pairs.
  /// Both trees are destructured simultaneously.
  static mylist<std::pair<uint64_t, uint64_t>> zip_trees(const tree &t1,
                                                         const tree &t2);
  static inline const uint64_t test_zip_trees = sum_list([]() {
    mylist<std::pair<uint64_t, uint64_t>> pairs = zip_trees(
        tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                   UINT64_C(2),
                   tree::node(tree::leaf(), UINT64_C(3), tree::leaf())),
        tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                   UINT64_C(20),
                   tree::node(tree::leaf(), UINT64_C(30), tree::leaf())));
    std::function<uint64_t(std::pair<uint64_t, uint64_t>)> add_pair =
        [](const std::pair<uint64_t, uint64_t> &p) {
          return (p.first + p.second);
        };
    if (std::holds_alternative<
            typename mylist<std::pair<uint64_t, uint64_t>>::Mynil>(
            pairs.v_mut())) {
      return mylist<uint64_t>::mycons(UINT64_C(0), mylist<uint64_t>::mynil());
    } else {
      auto &[a0, a1] =
          std::get<typename mylist<std::pair<uint64_t, uint64_t>>::Mycons>(
              pairs.v_mut());
      auto &&_sv0 = *a1;
      if (std::holds_alternative<
              typename mylist<std::pair<uint64_t, uint64_t>>::Mynil>(
              _sv0.v())) {
        return mylist<uint64_t>::mycons(add_pair(std::move(a0)),
                                        mylist<uint64_t>::mynil());
      } else {
        const auto &[a00, a10] =
            std::get<typename mylist<std::pair<uint64_t, uint64_t>>::Mycons>(
                _sv0.v());
        auto &&_sv1 = *a10;
        if (std::holds_alternative<
                typename mylist<std::pair<uint64_t, uint64_t>>::Mynil>(
                _sv1.v())) {
          return mylist<uint64_t>::mycons(
              add_pair(std::move(a0)),
              mylist<uint64_t>::mycons(add_pair(a00),
                                       mylist<uint64_t>::mynil()));
        } else {
          const auto &[a01, a11] =
              std::get<typename mylist<std::pair<uint64_t, uint64_t>>::Mycons>(
                  _sv1.v());
          return mylist<uint64_t>::mycons(
              add_pair(std::move(a0)),
              mylist<uint64_t>::mycons(
                  add_pair(a00),
                  mylist<uint64_t>::mycons(add_pair(a01),
                                           mylist<uint64_t>::mynil())));
        }
      }
    }
  }());
};

#endif // INCLUDED_MEM_SAFETY_PROBE24
