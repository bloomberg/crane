#ifndef INCLUDED_MEM_SAFETY_PROBE4
#define INCLUDED_MEM_SAFETY_PROBE4

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe4 {
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

    /// TEST 4: Partial app applied to recursive result, with a deeper tree.
    uint64_t tree_sum() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return ((a0->tree_sum() + a1) + a2->tree_sum());
      }
    }

    uint64_t sum_values(uint64_t x) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return x;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return (a1 + x);
        } else {
          const auto &[a00, a10, a20] = std::get<typename tree::Node>(_sv0.v());
          auto &&_sv1 = *a2;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            return (a10 + x);
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename tree::Node>(_sv1.v());
            return (((a10 + a11) + a1) + x);
          }
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

  /// TEST 1: Partial app applied to recursive result.
  /// The closure f captures tree t by &, but must survive across the
  /// recursive call in the loopified version.
  /// f(sum_through(xs)) requires f to be stored in a continuation frame.
  static uint64_t sum_through(const mylist<tree> &l);
  static inline const uint64_t test_sum_through =
      sum_through(mylist<tree>::mycons(
          tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
          mylist<tree>::mycons(
              tree::node(tree::leaf(), UINT64_C(20), tree::leaf()),
              mylist<tree>::mycons(
                  tree::node(tree::leaf(), UINT64_C(30), tree::leaf()),
                  mylist<tree>::mynil()))));
  /// TEST 2: Recursive result + partial app result.
  /// add_through(xs) + f(0): f might be pre-evaluated or stored in frame.
  static uint64_t add_through(const mylist<tree> &l);
  static inline const uint64_t test_add_through =
      add_through(mylist<tree>::mycons(
          tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
          mylist<tree>::mycons(
              tree::node(tree::leaf(), UINT64_C(20), tree::leaf()),
              mylist<tree>::mycons(
                  tree::node(tree::leaf(), UINT64_C(30), tree::leaf()),
                  mylist<tree>::mynil()))));
  /// TEST 3: Two partial apps from same tree, used around recursive call.
  static uint64_t double_partial(const mylist<tree> &l);
  static inline const uint64_t test_double_partial =
      double_partial(mylist<tree>::mycons(
          tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
          mylist<tree>::mycons(
              tree::node(tree::leaf(), UINT64_C(20), tree::leaf()),
              mylist<tree>::mynil())));
  static uint64_t weighted_sum(const mylist<tree> &l, uint64_t w);
  static inline const uint64_t test_weighted_sum = weighted_sum(
      mylist<tree>::mycons(
          tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
          mylist<tree>::mycons(
              tree::node(tree::leaf(), UINT64_C(20), tree::leaf()),
              mylist<tree>::mycons(
                  tree::node(tree::leaf(), UINT64_C(30), tree::leaf()),
                  mylist<tree>::mynil()))),
      UINT64_C(5)); /// TEST 5: Map building new trees from partial app results
                    /// across recursion.
  static mylist<uint64_t> transform_list(const mylist<tree> &l);
  static uint64_t mysum(const mylist<uint64_t> &l);
  static inline const uint64_t test_transform =
      mysum(transform_list(mylist<tree>::mycons(
          tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
          mylist<tree>::mycons(
              tree::node(tree::leaf(), UINT64_C(20), tree::leaf()),
              mylist<tree>::mycons(
                  tree::node(tree::leaf(), UINT64_C(30), tree::leaf()),
                  mylist<tree>::mynil())))));

  /// TEST 6: Recursive function where partial app is used as argument
  /// to a higher-order function alongside the recursive call.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t apply_to(F0 &&f, uint64_t _x0) {
    return f(_x0);
  }

  static uint64_t process_list(const mylist<tree> &l);
  static inline const uint64_t test_process_list =
      process_list(mylist<tree>::mycons(
          tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
          mylist<tree>::mycons(
              tree::node(tree::leaf(), UINT64_C(20), tree::leaf()),
              mylist<tree>::mycons(
                  tree::node(tree::leaf(), UINT64_C(30), tree::leaf()),
                  mylist<tree>::mynil()))));
  /// TEST 7: Nested recursion with closure capture across calls.
  static uint64_t nested_apply(const mylist<tree> &l, uint64_t base);
  static inline const uint64_t test_nested_apply = nested_apply(
      mylist<tree>::mycons(
          tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
          mylist<tree>::mycons(
              tree::node(tree::leaf(), UINT64_C(20), tree::leaf()),
              mylist<tree>::mycons(
                  tree::node(tree::leaf(), UINT64_C(30), tree::leaf()),
                  mylist<tree>::mynil()))),
      UINT64_C(0));
};

#endif // INCLUDED_MEM_SAFETY_PROBE4
