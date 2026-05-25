#ifndef INCLUDED_MEM_SAFETY_PROBE20
#define INCLUDED_MEM_SAFETY_PROBE20

#include <any>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe20 {
  /// Probe 20: Closures wrapped in data structures + if/match return.
  ///
  /// Attack vector: return_captures_by_value (translation.ml:1220-1227)
  /// only processes top-level Sreturn statements. If we wrap closures
  /// inside a data structure (preventing uncurrying) and return them
  /// from inside an if/match, the outer List.map matches s -> s
  /// and the lambdas remain &, creating dangling references.
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

  /// Wrapper type: wraps a closure in a data structure to prevent
  /// the function from being fully uncurried.
  struct wrapped {
    // DATA
    std::function<uint64_t(uint64_t)> a0;

    // ACCESSORS
    wrapped clone() const { return {a0}; }

    // CREATORS
    static wrapped wrap(std::function<uint64_t(uint64_t)> a0) {
      return {std::move(a0)};
    }

    uint64_t unwrap(uint64_t x) const {
      const auto &[a0] = *this;
      return a0(x);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &,
                                     std::function<uint64_t(uint64_t)> &>
    T1 wrapped_rec(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &,
                                     std::function<uint64_t(uint64_t)> &>
    T1 wrapped_rect(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }
  };

  /// TEST 1: Return wrapped closure from if-branch.
  /// The if becomes top-level Sif. return_captures_by_value sees
  /// Sif, matches s -> s, leaves lambda as &.
  static wrapped wrap_if(tree t, bool b);
  static inline const uint64_t test_wrap_if = []() {
    wrapped w =
        wrap_if(tree::node(tree::leaf(), UINT64_C(42), tree::leaf()), true);
    return std::move(w).unwrap(UINT64_C(0));
  }();
  /// TEST 2: Return wrapped closure from match on custom type.
  enum class Choice { CLEFT, CRIGHT };

  template <typename T1> static T1 choice_rect(T1 f, T1 f0, Choice c) {
    switch (c) {
    case Choice::CLEFT: {
      return f;
    }
    case Choice::CRIGHT: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 choice_rec(T1 f, T1 f0, Choice c) {
    switch (c) {
    case Choice::CLEFT: {
      return f;
    }
    case Choice::CRIGHT: {
      return f0;
    }
    default:
      std::unreachable();
    }
  }

  static wrapped wrap_match(tree t, Choice c);
  static inline const uint64_t test_wrap_match = []() {
    wrapped w = wrap_match(
        tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                   UINT64_C(7), tree::leaf()),
        Choice::CLEFT);
    return std::move(w).unwrap(UINT64_C(0));
  }();
  /// TEST 3: Pair of closure and value, returned from if.
  /// Uses prod to wrap the closure.
  static std::pair<wrapped, uint64_t> pair_from_if(tree t, bool b);
  static inline const uint64_t test_pair_if = []() {
    std::pair<wrapped, uint64_t> p = pair_from_if(
        tree::node(tree::leaf(), UINT64_C(15), tree::leaf()), true);
    wrapped w = p.first;
    uint64_t v = p.second;
    return std::move(w).unwrap(v);
  }();
  /// TEST 4: Wrapped closure captured in a locally-constructed tree.
  /// The let-bound tree is stack-allocated.
  static wrapped wrap_local(uint64_t n, bool b);
  static inline const uint64_t test_wrap_local = []() {
    wrapped w = wrap_local(UINT64_C(20), true);
    return std::move(w).unwrap(UINT64_C(5));
  }();
  /// TEST 5: Double use of unwrapped closure.
  static inline const uint64_t test_double_unwrap = []() {
    wrapped w =
        wrap_if(tree::node(tree::leaf(), UINT64_C(7), tree::leaf()), true);
    return (w.unwrap(UINT64_C(1)) + w.unwrap(UINT64_C(2)));
  }();
  /// TEST 6: Nested wrapped closure: wrapped inside a pair inside if.
  static wrapped nested_wrap(tree t, bool b1, bool b2);
  static inline const uint64_t test_nested_wrap = []() {
    wrapped w = nested_wrap(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                            true, false);
    return std::move(w).unwrap(UINT64_C(0));
  }(); /// TEST 7: List of wrapped closures from if branches.

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

  static mylist<wrapped> wrap_list(tree t, bool b);
  static uint64_t sum_wrapped(const mylist<wrapped> &l, uint64_t x);
  static inline const uint64_t test_wrap_list = []() {
    mylist<wrapped> l =
        wrap_list(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()), true);
    return sum_wrapped(std::move(l), UINT64_C(0));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE20
