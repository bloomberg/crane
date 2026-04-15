#ifndef INCLUDED_CPS_ESCAPE
#define INCLUDED_CPS_ESCAPE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct CpsEscape {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> d_a0;
      unsigned int d_a1;
      std::shared_ptr<tree> d_a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(Leaf _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree> leaf() {
      return std::make_shared<tree>(Leaf{});
    }

    static std::shared_ptr<tree> node(const std::shared_ptr<tree> &a0,
                                      unsigned int a1,
                                      const std::shared_ptr<tree> &a2) {
      return std::make_shared<tree>(Node{a0, std::move(a1), a2});
    }

    static std::shared_ptr<tree> node(std::shared_ptr<tree> &&a0,
                                      unsigned int a1,
                                      std::shared_ptr<tree> &&a2) {
      return std::make_shared<tree>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// CPS-style: take a tree, produce a continuation (nat -> nat)
    /// that adds tree_sum to its argument. The continuation captures t.
    __attribute__((pure)) unsigned int make_adder(const unsigned int x) const {
      return (this->tree_sum() + x);
    }

    /// Sum all values in a tree.
    __attribute__((pure)) unsigned int tree_sum() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::Node>(this->v());
        return ((d_a0->tree_sum() + d_a1) + d_a2->tree_sum());
      }
    }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    if (std::holds_alternative<typename tree::Leaf>(t->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t->v());
      return f0(d_a0, tree_rect<T1>(f, f0, d_a0), d_a1, d_a2,
                tree_rect<T1>(f, f0, d_a2));
    }
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    if (std::holds_alternative<typename tree::Leaf>(t->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t->v());
      return f0(d_a0, tree_rec<T1>(f, f0, d_a0), d_a1, d_a2,
                tree_rec<T1>(f, f0, d_a2));
    }
  }

  struct box {
    // TYPES
    struct Box0 {
      std::function<unsigned int(unsigned int)> d_a0;
    };

    using variant_t = std::variant<Box0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit box(Box0 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<box>
    box0(std::function<unsigned int(unsigned int)> a0) {
      return std::make_shared<box>(Box0{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1,
              MapsTo<T1, std::function<unsigned int(unsigned int)>> F0>
    T1 box_rec(F0 &&f) const {
      const auto &[d_a0] = std::get<typename box::Box0>(this->v());
      return f(d_a0);
    }

    template <typename T1,
              MapsTo<T1, std::function<unsigned int(unsigned int)>> F0>
    T1 box_rect(F0 &&f) const {
      const auto &[d_a0] = std::get<typename box::Box0>(this->v());
      return f(d_a0);
    }
  };

  /// Store the continuation in a Box. The function receives the closure
  /// as an argument and wraps it - the closure flows THROUGH a parameter.
  template <MapsTo<unsigned int, unsigned int> F0>
  static std::shared_ptr<box> store_in_box(F0 &&f) {
    return box::box0(f);
  }

  /// BUG HYPOTHESIS: make_adder creates &t lambda.
  /// store_in_box receives it and puts it in Box.
  /// When cps_escape returns, t is destroyed but Box holds the lambda.
  ///
  /// Expected: tree_sum(Node(Node(Leaf,10,Leaf), 20, Node(Leaf,30,Leaf)))
  /// = 10 + 20 + 30 = 60
  /// adder 5 = 60 + 5 = 65
  static inline const unsigned int cps_escape = []() {
    return []() {
      std::shared_ptr<tree> t =
          tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                     tree::node(tree::leaf(), 30u, tree::leaf()));
      std::function<unsigned int(unsigned int)> adder =
          [=](unsigned int _x0) mutable -> unsigned int {
        return t->make_adder(_x0);
      };
      std::shared_ptr<box> b = store_in_box(adder);
      const auto &[d_a0] = std::get<typename box::Box0>(b->v());
      return d_a0(5u);
    }();
  }();
  /// Same but inline: no intermediate let for adder.
  /// The closure goes directly from make_adder into store_in_box.
  static inline const unsigned int cps_escape_inline = []() {
    return []() {
      std::shared_ptr<tree> t =
          tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                     tree::node(tree::leaf(), 30u, tree::leaf()));
      std::shared_ptr<box> b =
          store_in_box([=](unsigned int _x0) mutable -> unsigned int {
            return t->make_adder(_x0);
          });
      const auto &[d_a0] = std::get<typename box::Box0>(b->v());
      return d_a0(5u);
    }();
  }();
  /// CPS with two stored continuations.
  /// Build two adders from different trees and store both.
  static inline const unsigned int cps_escape_two = []() {
    return []() {
      std::shared_ptr<tree> t1 =
          tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                     tree::node(tree::leaf(), 30u, tree::leaf()));
      std::shared_ptr<tree> t2 = tree::node(tree::leaf(), 100u, tree::leaf());
      std::shared_ptr<box> b1 =
          store_in_box([=](unsigned int _x0) mutable -> unsigned int {
            return t1->make_adder(_x0);
          });
      std::shared_ptr<box> b2 =
          store_in_box([=](unsigned int _x0) mutable -> unsigned int {
            return t2->make_adder(_x0);
          });
      const auto &[d_a0] = std::get<typename box::Box0>(b1->v());
      const auto &[d_a00] = std::get<typename box::Box0>(b2->v());
      return (d_a0(0u) + d_a00(0u));
    }();
  }();
};

#endif // INCLUDED_CPS_ESCAPE
