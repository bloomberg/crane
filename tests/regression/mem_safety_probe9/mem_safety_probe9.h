#ifndef INCLUDED_MEM_SAFETY_PROBE9
#define INCLUDED_MEM_SAFETY_PROBE9

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe9 {
  /// These tests probe patterns where closures accumulate
  /// during tree traversal. Each closure captures subtrees
  /// (unique_ptr fields) that are also used in recursive calls.
  /// The captures must be independent clones.
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

    /// TEST 5: Mutual use pattern — the left subtree is used to compute
    /// a value that's passed to a closure that captures the right subtree.
    uint64_t cross_capture() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        uint64_t lsum = a0_value.tree_sum();
        std::function<uint64_t(uint64_t)> f = [=](uint64_t n) mutable {
          return (a2_value.tree_sum() + n);
        };
        return (f(lsum) + f(a1));
      }
    }

    /// TEST 4: Closures that capture a tree AND its subtrees
    /// independently — tests that cloning produces independent
    /// copies. Modify one subtree's computation after capture.
    uint64_t triple_capture() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return ((_anon_f1(UINT64_C(0), *a0) + _anon_f2(UINT64_C(0), *a2)) +
                _anon_f3(UINT64_C(0), *this));
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

  template <typename T1> static uint64_t _anon_f1(const T1, const tree l) {
    return l.tree_sum();
  }

  template <typename T1> static uint64_t _anon_f2(const T1, const tree r) {
    return std::move(r).tree_sum();
  }

  template <typename T1> static uint64_t _anon_f3(const T1, const tree t) {
    return t.tree_sum();
  }

  static uint64_t sum_fns(const mylist<std::function<uint64_t(uint64_t)>> &l);

  /// TEST 1: Collect closures that each capture a subtree.
  /// Both l and r are captured AND used in recursive calls.
  template <typename T1>
  static uint64_t _collect_subtree_sums_f(const T1, const tree l,
                                          const uint64_t v, const tree r) {
    return ((std::move(l).tree_sum() + v) + r.tree_sum());
  }

  static mylist<std::function<uint64_t(uint64_t)>>
  collect_subtree_sums(const tree &t,
                       mylist<std::function<uint64_t(uint64_t)>> acc);
  static inline const uint64_t test_collect = []() {
    tree t = tree::node(
        tree::node(tree::leaf(), UINT64_C(5), tree::leaf()), UINT64_C(10),
        tree::node(tree::leaf(), UINT64_C(15),
                   tree::node(tree::leaf(), UINT64_C(20), tree::leaf())));
    mylist<std::function<uint64_t(uint64_t)>> fns = collect_subtree_sums(
        std::move(t), mylist<std::function<uint64_t(uint64_t)>>::mynil());
    return sum_fns(std::move(fns));
  }();

  /// TEST 2: Similar but each closure captures ONLY the left subtree.
  /// The left subtree is shared between closure and recursive call.
  template <typename T1>
  static uint64_t _collect_left_sums_f(const T1, const tree l) {
    return std::move(l).tree_sum();
  }

  static mylist<std::function<uint64_t(uint64_t)>>
  collect_left_sums(const tree &t,
                    mylist<std::function<uint64_t(uint64_t)>> acc);
  static inline const uint64_t test_left_sums = []() {
    tree t = tree::node(
        tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                   UINT64_C(7), tree::leaf()),
        UINT64_C(10), tree::node(tree::leaf(), UINT64_C(15), tree::leaf()));
    mylist<std::function<uint64_t(uint64_t)>> fns = collect_left_sums(
        std::move(t), mylist<std::function<uint64_t(uint64_t)>>::mynil());
    return sum_fns(std::move(fns));
  }();

  /// TEST 3: Build closures from list where each closure
  /// captures the tail and a computed value.
  template <typename T1>
  static uint64_t _list_accum_closures_f(const T1, const uint64_t x,
                                         const uint64_t tail_len) {
    return (std::move(x) * tail_len);
  }

  static mylist<std::function<uint64_t(uint64_t)>>
  list_accum_closures(const mylist<uint64_t> &l,
                      mylist<std::function<uint64_t(uint64_t)>> acc);
  static inline const uint64_t test_list_accum = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(10),
        mylist<uint64_t>::mycons(
            UINT64_C(20),
            mylist<uint64_t>::mycons(UINT64_C(30), mylist<uint64_t>::mynil())));
    mylist<std::function<uint64_t(uint64_t)>> fns = list_accum_closures(
        std::move(l), mylist<std::function<uint64_t(uint64_t)>>::mynil());
    return sum_fns(std::move(fns));
  }();
  static inline const uint64_t test_triple =
      tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                 UINT64_C(20),
                 tree::node(tree::leaf(), UINT64_C(30), tree::leaf()))
          .triple_capture();
  static inline const uint64_t test_cross =
      tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                 UINT64_C(10),
                 tree::node(tree::leaf(), UINT64_C(15), tree::leaf()))
          .cross_capture();
  /// TEST 6: Stress test — large tree, many closures.
  static tree make_balanced(uint64_t n);
  static inline const uint64_t test_stress = []() {
    tree t = make_balanced(UINT64_C(5));
    mylist<std::function<uint64_t(uint64_t)>> fns = collect_left_sums(
        std::move(t), mylist<std::function<uint64_t(uint64_t)>>::mynil());
    return sum_fns(std::move(fns));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE9
