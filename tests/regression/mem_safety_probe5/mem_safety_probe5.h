#ifndef INCLUDED_MEM_SAFETY_PROBE5
#define INCLUDED_MEM_SAFETY_PROBE5

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe5 {
  /// These tests probe interactions between:
  /// - Closures that access nested fields of value types
  /// - Loopification storing closures in frames
  /// - The body_derefs_var override in cpp_print.ml
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

    /// TEST 4: Deep tree with closures at each level.
    uint64_t tree_size() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return ((UINT64_C(1) + a0->tree_size()) + a2->tree_size());
      }
    }

    /// TEST 3: Pair a partial app with its tree, use both after
    /// the tree might have been moved.
    uint64_t pair_and_apply() const {
      tree _self_val = *this;
      std::function<uint64_t(uint64_t)> f =
          [=](uint64_t _x0) mutable -> uint64_t {
        return _self_val.get_left_val(_x0);
      };
      uint64_t v = [&]() {
        if (std::holds_alternative<typename tree::Leaf>(this->v())) {
          return UINT64_C(0);
        } else {
          auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
          return a1;
        }
      }();
      return f(v);
    }

    /// A function that accesses a NESTED field — forces a
    /// dereference of a unique_ptr inside the lambda body.
    uint64_t get_left_val(uint64_t default0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return default0;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return default0;
        } else {
          const auto &[a00, a10, a20] = std::get<typename tree::Node>(_sv0.v());
          return a10;
        }
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

  /// TEST 1: Partial app of get_left_val, applied to recursive result.
  /// The closure body accesses nested tree structure.
  static uint64_t sum_left_vals(const mylist<tree> &l);
  static inline const uint64_t test_sum_left =
      sum_left_vals(mylist<tree>::mycons(
          tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                     UINT64_C(20), tree::leaf()),
          mylist<tree>::mycons(
              tree::node(tree::node(tree::leaf(), UINT64_C(30), tree::leaf()),
                         UINT64_C(40), tree::leaf()),
              mylist<tree>::mycons(
                  tree::node(tree::leaf(), UINT64_C(50), tree::leaf()),
                  mylist<tree>::mynil()))));
  /// TEST 2: Build a list of partial apps from trees, then apply all.
  /// Each partial app captures a tree with nested structure.
  static mylist<std::function<uint64_t(uint64_t)>>
  build_getters(const mylist<tree> &l);
  static uint64_t apply_all(const mylist<std::function<uint64_t(uint64_t)>> &l,
                            uint64_t x);
  static inline const uint64_t test_build_apply = []() {
    mylist<tree> trees = mylist<tree>::mycons(
        tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                   UINT64_C(20), tree::leaf()),
        mylist<tree>::mycons(
            tree::node(tree::node(tree::leaf(), UINT64_C(30), tree::leaf()),
                       UINT64_C(40), tree::leaf()),
            mylist<tree>::mycons(
                tree::node(tree::leaf(), UINT64_C(50), tree::leaf()),
                mylist<tree>::mynil())));
    mylist<std::function<uint64_t(uint64_t)>> getters =
        build_getters(std::move(trees));
    return apply_all(std::move(getters), UINT64_C(0));
  }();
  static inline const uint64_t test_pair_apply =
      tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                 UINT64_C(20), tree::leaf())
          .pair_and_apply();
  static mylist<std::function<uint64_t(uint64_t)>>
  collect_left_vals(tree t, mylist<std::function<uint64_t(uint64_t)>> acc);
  static inline const uint64_t test_collect = []() {
    tree t = tree::node(
        tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                   UINT64_C(10), tree::leaf()),
        UINT64_C(15),
        tree::node(tree::leaf(), UINT64_C(20),
                   tree::node(tree::leaf(), UINT64_C(25), tree::leaf())));
    mylist<std::function<uint64_t(uint64_t)>> fns = collect_left_vals(
        std::move(t), mylist<std::function<uint64_t(uint64_t)>>::mynil());
    return apply_all(std::move(fns), UINT64_C(0));
  }();
  /// TEST 6: Stress test with very large list of trees.
  static mylist<tree> make_tree_list(uint64_t n);
  static uint64_t
  sum_getters(const mylist<std::function<uint64_t(uint64_t)>> &l, uint64_t x);
  static inline const uint64_t test_stress = []() {
    mylist<tree> trees = make_tree_list(UINT64_C(50));
    mylist<std::function<uint64_t(uint64_t)>> getters =
        build_getters(std::move(trees));
    return sum_getters(std::move(getters), UINT64_C(0));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE5
