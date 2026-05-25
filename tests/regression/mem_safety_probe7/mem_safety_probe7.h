#ifndef INCLUDED_MEM_SAFETY_PROBE7
#define INCLUDED_MEM_SAFETY_PROBE7

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe7 {
  /// These tests FORCE closures that capture recursive self-reference
  /// fields (unique_ptr) by storing them in data structures.
  /// Closures return SCALAR values but COMPUTE from captured
  /// recursive structures (lists/trees).
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
  /// TEST 1: Build a list of closures where each captures the TAIL
  /// and computes its length. The tail is unique_ptr.
  static mylist<std::function<uint64_t(std::monostate)>>
  build_len_closures(const mylist<uint64_t> &l);
  static uint64_t
  sum_fns(const mylist<std::function<uint64_t(std::monostate)>> &l);
  static inline const uint64_t test_len_closures = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(1),
        mylist<uint64_t>::mycons(
            UINT64_C(2),
            mylist<uint64_t>::mycons(
                UINT64_C(3), mylist<uint64_t>::mycons(
                                 UINT64_C(4), mylist<uint64_t>::mynil()))));
    mylist<std::function<uint64_t(std::monostate)>> fns =
        build_len_closures(std::move(l));
    return sum_fns(std::move(fns));
  }();
  /// TEST 2: Build closures that compute the SUM of the tail.
  /// Each closure captures the entire tail sublist.
  static mylist<std::function<uint64_t(std::monostate)>>
  build_sum_closures(const mylist<uint64_t> &l);
  static inline const uint64_t test_sum_closures = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(10),
        mylist<uint64_t>::mycons(
            UINT64_C(20),
            mylist<uint64_t>::mycons(UINT64_C(30), mylist<uint64_t>::mynil())));
    mylist<std::function<uint64_t(std::monostate)>> fns =
        build_sum_closures(std::move(l));
    return sum_fns(std::move(fns));
  }();

  /// Sums: sum20,30=50, sum30=30, sum=0. Total = 80.
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

    /// TEST 5: Create closures that capture BOTH children of a tree
    /// and use them independently. Both l and r are unique_ptr.
    std::pair<std::function<uint64_t(std::monostate)>,
              std::function<uint64_t(std::monostate)>>
    make_subtree_getters() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair([](std::monostate) { return UINT64_C(0); },
                              [](std::monostate) { return UINT64_C(0); });
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        return std::make_pair(
            [=](std::monostate) mutable { return a0_value.tree_sum(); },
            [=](std::monostate) mutable { return a2_value.tree_sum(); });
      }
    }

    /// TEST 3: Build closures from tree that each capture a subtree
    /// and compute its sum.
    mylist<std::function<uint64_t(std::monostate)>> tree_sum_closures() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return mylist<std::function<uint64_t(std::monostate)>>::mynil();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        return mylist<std::function<uint64_t(std::monostate)>>::mycons(
            [=](std::monostate) mutable { return a0_value.tree_sum(); },
            mylist<std::function<uint64_t(std::monostate)>>::mycons(
                [=](std::monostate) mutable { return a2_value.tree_sum(); },
                mylist<std::function<uint64_t(std::monostate)>>::mynil()));
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

  static inline const uint64_t test_tree_closures = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    mylist<std::function<uint64_t(std::monostate)>> fns =
        std::move(t).tree_sum_closures();
    return sum_fns(std::move(fns));
  }();
  /// TEST 4: Each closure captures the tail AND the current value.
  /// After building all closures, call them — the captured lists
  /// must be independent copies.
  static mylist<std::function<uint64_t(uint64_t)>>
  build_accum_closures(const mylist<uint64_t> &l);
  static uint64_t apply_all(const mylist<std::function<uint64_t(uint64_t)>> &l,
                            uint64_t x);
  static inline const uint64_t test_accum_closures = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(1),
        mylist<uint64_t>::mycons(
            UINT64_C(2),
            mylist<uint64_t>::mycons(UINT64_C(3), mylist<uint64_t>::mynil())));
    mylist<std::function<uint64_t(uint64_t)>> fns =
        build_accum_closures(std::move(l));
    return apply_all(std::move(fns), UINT64_C(0));
  }();
  static inline const uint64_t test_subtree_getters = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    std::pair<std::function<uint64_t(std::monostate)>,
              std::function<uint64_t(std::monostate)>>
        p = std::move(t).make_subtree_getters();
    return (p.first(std::monostate{}) + p.second(std::monostate{}));
  }();
  /// TEST 6: Stress test — large list, each closure captures
  /// the entire remaining tail.
  static mylist<uint64_t> make_nat_list(uint64_t n);
  static inline const uint64_t test_stress_closures = []() {
    mylist<uint64_t> l = make_nat_list(UINT64_C(20));
    mylist<std::function<uint64_t(std::monostate)>> fns =
        build_len_closures(std::move(l));
    return sum_fns(std::move(fns));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE7
