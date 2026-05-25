#ifndef INCLUDED_MEM_SAFETY_PROBE17
#define INCLUDED_MEM_SAFETY_PROBE17

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe17 {
  /// Probe 17: Wide tree (4-ary) and complex ownership patterns.
  ///
  /// Attack vectors:
  /// 1. 4-ary tree with 4 unique_ptr children -- more complex frame structs
  /// 2. Functions that use ALL children in computations AND recursive calls
  /// 3. Owned match where one child is used in a closure AND others
  /// in recursive calls (testing pre-extraction with many children)
  /// 4. Mutual-like patterns where different functions process the
  /// same tree differently
  struct qtree {
    // TYPES
    struct QLeaf {};

    struct QNode {
      std::shared_ptr<qtree> a0;
      std::shared_ptr<qtree> a1;
      uint64_t a2;
      std::shared_ptr<qtree> a3;
      std::shared_ptr<qtree> a4;
    };

    using variant_t = std::variant<QLeaf, QNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    qtree() {}

    explicit qtree(QLeaf _v) : v_(_v) {}

    explicit qtree(QNode _v) : v_(std::move(_v)) {}

    static qtree qleaf() { return qtree(QLeaf{}); }

    static qtree qnode(qtree a0, qtree a1, uint64_t a2, qtree a3, qtree a4) {
      return qtree(QNode{std::make_shared<qtree>(std::move(a0)),
                         std::make_shared<qtree>(std::move(a1)), a2,
                         std::make_shared<qtree>(std::move(a3)),
                         std::make_shared<qtree>(std::move(a4))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// TEST 6: Compute a value using ALL children non-recursively,
    /// THEN use all children recursively. Tests frame saving with
    /// many unique_ptr fields.
    uint64_t weighted_sum() const {
      if (std::holds_alternative<typename qtree::QLeaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename qtree::QNode>(this->v());
        uint64_t local_weight =
            ((((a0->qtree_sum() + (UINT64_C(2) * a1->qtree_sum())) +
               (UINT64_C(3) * a2)) +
              (UINT64_C(4) * a3->qtree_sum())) +
             (UINT64_C(5) * a4->qtree_sum()));
        return ((((local_weight + a0->weighted_sum()) + a1->weighted_sum()) +
                 a3->weighted_sum()) +
                a4->weighted_sum());
      }
    }

    /// TEST 5: Zip two 4-ary trees.
    qtree qtree_zip(qtree t2) const {
      if (std::holds_alternative<typename qtree::QLeaf>(this->v())) {
        return t2;
      } else {
        auto &[a0, a2, a3, a4, a5] = std::get<typename qtree::QNode>(this->v());
        if (std::holds_alternative<typename qtree::QLeaf>(t2.v_mut())) {
          return *this;
        } else {
          auto &[a00, a10, a20, a30, a40] =
              std::get<typename qtree::QNode>(t2.v_mut());
          return qtree::qnode(a0->qtree_zip(*a00), a2->qtree_zip(*a10),
                              (std::move(a3) + std::move(a20)),
                              a4->qtree_zip(*a30), a5->qtree_zip(*a40));
        }
      }
    }

    /// TEST 3: Mirror a 4-ary tree (reverse children order).
    qtree qtree_mirror() const {
      if (std::holds_alternative<typename qtree::QLeaf>(this->v())) {
        return qtree::qleaf();
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename qtree::QNode>(this->v());
        return qtree::qnode(a4->qtree_mirror(), a3->qtree_mirror(), a2,
                            a1->qtree_mirror(), a0->qtree_mirror());
      }
    }

    uint64_t qtree_size() const {
      if (std::holds_alternative<typename qtree::QLeaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename qtree::QNode>(this->v());
        return ((((UINT64_C(1) + a0->qtree_size()) + a1->qtree_size()) +
                 a3->qtree_size()) +
                a4->qtree_size());
      }
    }

    uint64_t qtree_depth() const {
      if (std::holds_alternative<typename qtree::QLeaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename qtree::QNode>(this->v());
        uint64_t da = a0->qtree_depth();
        uint64_t db = a1->qtree_depth();
        uint64_t dc = a3->qtree_depth();
        uint64_t dd = a4->qtree_depth();
        uint64_t m1;
        if (da <= db) {
          m1 = db;
        } else {
          m1 = da;
        }
        uint64_t m2;
        if (dc <= dd) {
          m2 = dd;
        } else {
          m2 = dc;
        }
        return (UINT64_C(1) + (m1 <= m2 ? m2 : m1));
      }
    }

    uint64_t qtree_sum() const {
      if (std::holds_alternative<typename qtree::QLeaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename qtree::QNode>(this->v());
        return ((((a0->qtree_sum() + a1->qtree_sum()) + a2) + a3->qtree_sum()) +
                a4->qtree_sum());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, qtree &, T1 &, qtree &, T1 &,
                                     uint64_t &, qtree &, T1 &, qtree &, T1 &>
    T1 qtree_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename qtree::QLeaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename qtree::QNode>(this->v());
        return f0(*a0, a0->template qtree_rec<T1>(f, f0), *a1,
                  a1->template qtree_rec<T1>(f, f0), a2, *a3,
                  a3->template qtree_rec<T1>(f, f0), *a4,
                  a4->template qtree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, qtree &, T1 &, qtree &, T1 &,
                                     uint64_t &, qtree &, T1 &, qtree &, T1 &>
    T1 qtree_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename qtree::QLeaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2, a3, a4] =
            std::get<typename qtree::QNode>(this->v());
        return f0(*a0, a0->template qtree_rect<T1>(f, f0), *a1,
                  a1->template qtree_rect<T1>(f, f0), a2, *a3,
                  a3->template qtree_rect<T1>(f, f0), *a4,
                  a4->template qtree_rect<T1>(f, f0));
      }
    }
  };

  /// TEST 1: Sum of a 4-ary tree. Basic correctness.
  static inline const uint64_t test_qtree_sum = []() {
    qtree t =
        qtree::qnode(qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(1),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(2),
                                  qtree::qleaf(), qtree::qleaf()),
                     UINT64_C(10),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(3),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(4),
                                  qtree::qleaf(), qtree::qleaf()));
    return std::move(t).qtree_sum();
  }();
  /// TEST 2: Depth of a deep 4-ary tree.
  static inline const uint64_t test_qtree_depth = []() {
    qtree inner = qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(1),
                               qtree::qleaf(), qtree::qleaf());
    qtree t = qtree::qnode(inner,
                           qtree::qnode(inner, qtree::qleaf(), UINT64_C(2),
                                        qtree::qleaf(), qtree::qleaf()),
                           UINT64_C(3), qtree::qleaf(), qtree::qleaf());
    return std::move(t).qtree_depth();
  }();
  static inline const uint64_t test_qtree_mirror = []() {
    qtree t =
        qtree::qnode(qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(1),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qleaf(), UINT64_C(10),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(3),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qleaf());
    return std::move(t).qtree_mirror().qtree_sum();
  }();

  /// TEST 4: Flatten a 4-ary tree to a list (inorder traversal).
  /// Uses all 4 children in recursive calls + value in list construction.
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
  static mylist<uint64_t> qtree_flatten(const qtree &t);
  static inline const uint64_t test_qtree_flatten = []() {
    qtree t =
        qtree::qnode(qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(1),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(2),
                                  qtree::qleaf(), qtree::qleaf()),
                     UINT64_C(5),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(3),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(4),
                                  qtree::qleaf(), qtree::qleaf()));
    return sum_list(qtree_flatten(std::move(t)));
  }();
  static inline const uint64_t test_qtree_zip = []() {
    qtree t1 = qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(10),
                            qtree::qleaf(), qtree::qleaf());
    qtree t2 = qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(20),
                            qtree::qleaf(), qtree::qleaf());
    return std::move(t1).qtree_zip(std::move(t2)).qtree_sum();
  }();
  static inline const uint64_t test_weighted = []() {
    qtree t =
        qtree::qnode(qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(1),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(2),
                                  qtree::qleaf(), qtree::qleaf()),
                     UINT64_C(3),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(4),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(5),
                                  qtree::qleaf(), qtree::qleaf()));
    return std::move(t).weighted_sum();
  }();
  /// TEST 7: Build a 4-ary tree programmatically and check.
  static qtree make_qtree(uint64_t n);
  static inline const uint64_t test_make_qtree =
      make_qtree(UINT64_C(4)).qtree_sum();
  /// TEST 8: Two-pass on a 4-ary tree: flatten then sum vs direct sum.
  static inline const uint64_t test_two_pass_qtree = []() {
    qtree t =
        qtree::qnode(qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(1),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(2),
                                  qtree::qleaf(), qtree::qleaf()),
                     UINT64_C(5),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(3),
                                  qtree::qleaf(), qtree::qleaf()),
                     qtree::qnode(qtree::qleaf(), qtree::qleaf(), UINT64_C(4),
                                  qtree::qleaf(), qtree::qleaf()));
    return (sum_list(qtree_flatten(t)) + t.qtree_sum());
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE17
