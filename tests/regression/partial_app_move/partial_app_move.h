#ifndef INCLUDED_PARTIAL_APP_MOVE
#define INCLUDED_PARTIAL_APP_MOVE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct PartialAppMove {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree> d_a0;
      unsigned int d_a1;
      std::unique_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    tree(const tree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree(tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) tree &operator=(const tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) tree &operator=(tree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) tree clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        return tree(Leaf{});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
        return tree(
            Node{d_a0 ? std::make_unique<PartialAppMove::tree>(d_a0->clone())
                      : nullptr,
                 [](auto &&__v) -> unsigned int {
                   if constexpr (
                       requires { __v ? 0 : 0; } && requires { *__v; } &&
                       requires { __v->clone(); } && requires { __v.get(); }) {
                     using _E = std::remove_cvref_t<decltype(*__v)>;
                     return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
                   } else if constexpr (requires { __v.clone(); }) {
                     return __v.clone();
                   } else {
                     return __v;
                   }
                 }(d_a1),
                 d_a2 ? std::make_unique<PartialAppMove::tree>(d_a2->clone())
                      : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree leaf() { return tree(Leaf{}); }

    __attribute__((pure)) static tree node(const tree &a0, unsigned int a1,
                                           const tree &a2) {
      return tree(Node{std::make_unique<tree>(a0), std::move(a1),
                       std::make_unique<tree>(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) tree *operator->() { return this; }

    __attribute__((pure)) const tree *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = tree(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rect<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rect<T1>(f, f0, *(d_a2)));
    }
  }

  template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rec<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rec<T1>(f, f0, *(d_a2)));
    }
  }

  /// A function taking two args: tree -> nat -> nat.
  /// Partial application of this to a tree creates a
  /// closure nat -> nat in C++ via & lambda.
  __attribute__((pure)) static unsigned int sum_values(const tree &t,
                                                       unsigned int x);
  /// Wrap a tree inside another Node.
  /// In C++, this calls tree::node() which has rvalue ref overloads.
  /// If escape analysis adds std::move(t) here, the move is REAL.
  __attribute__((pure)) static tree wrap(tree t);
  /// BUG TRIGGER: partial application creates a & lambda capturing t,
  /// then t is passed to a constructor (actually moved via rvalue ref),
  /// then the lambda accesses the moved-from t.
  __attribute__((pure)) static unsigned int trigger_bug(tree t);
  /// Build a tree and trigger the bug.
  static inline const unsigned int run_bug =
      trigger_bug(tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                             tree::node(tree::leaf(), 30u, tree::leaf())));
  /// Inline version: t is a local variable, not a function parameter.
  /// This is where move optimization might actually move t.
  static inline const unsigned int inline_bug = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                          tree::node(tree::leaf(), 30u, tree::leaf()));
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return sum_values(t, _x0);
      };
      tree w = tree::node(t, 42u, tree::leaf());
      if (std::holds_alternative<typename tree::Leaf>(w.v())) {
        return f(0u);
      } else {
        return f(99u);
      }
    }();
  }();
  /// Same but using wrap function.
  static inline const unsigned int inline_bug2 = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                          tree::node(tree::leaf(), 30u, tree::leaf()));
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return sum_values(t, _x0);
      };
      tree w = wrap(t);
      if (std::holds_alternative<typename tree::Leaf>(w.v())) {
        return f(0u);
      } else {
        return f(99u);
      }
    }();
  }();
};

#endif // INCLUDED_PARTIAL_APP_MOVE
