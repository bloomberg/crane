#ifndef INCLUDED_METHOD_PARTIAL_APP
#define INCLUDED_METHOD_PARTIAL_APP

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct MethodPartialApp {
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

    /// add_to_sum: methodified on first arg (tree).
    /// Takes a tree and a nat, returns the tree's sum plus the nat.
    __attribute__((pure)) unsigned int add_to_sum(const unsigned int x) const {
      return (this->tree_sum() + x);
    }

    __attribute__((pure)) unsigned int tree_sum() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::Node>(this->v());
        return ((d_a0->tree_sum() + d_a1) + d_a2->tree_sum());
      }
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                  std::shared_ptr<tree>, T1>
                               F1>
    T1 tree_rec(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::Node>(this->v());
        return f0(d_a0, d_a0->template tree_rec<T1>(f, f0), d_a1, d_a2,
                  d_a2->template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                  std::shared_ptr<tree>, T1>
                               F1>
    T1 tree_rect(const T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::Node>(this->v());
        return f0(d_a0, d_a0->template tree_rect<T1>(f, f0), d_a1, d_a2,
                  d_a2->template tree_rect<T1>(f, f0));
      }
    }
  };

  /// Direct partial app stored in let, called twice.
  static inline const unsigned int method_partial_bug = []() {
    return []() {
      std::shared_ptr<tree> t =
          tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                     tree::node(tree::leaf(), 30u, tree::leaf()));
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return t->add_to_sum(_x0);
      };
      return (f(5u) + f(10u));
    }();
  }();

  /// Partial app stored in a constructor.
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

  static inline const unsigned int method_partial_box = []() {
    return []() {
      std::shared_ptr<tree> t =
          tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                     tree::node(tree::leaf(), 30u, tree::leaf()));
      std::shared_ptr<box> b =
          box::box0([=](unsigned int _x0) mutable -> unsigned int {
            return t->add_to_sum(_x0);
          });
      const auto &[d_a0] = std::get<typename box::Box0>(b->v());
      return (d_a0(5u) + d_a0(10u));
    }();
  }();
  /// Two partial apps from different trees.
  static inline const unsigned int method_partial_two = []() {
    return []() {
      std::shared_ptr<tree> t1 = tree::node(tree::leaf(), 10u, tree::leaf());
      std::shared_ptr<tree> t2 = tree::node(tree::leaf(), 20u, tree::leaf());
      std::function<unsigned int(unsigned int)> f1 =
          [&](unsigned int _x0) -> unsigned int {
        return std::move(t1)->add_to_sum(_x0);
      };
      std::function<unsigned int(unsigned int)> f2 =
          [&](unsigned int _x0) -> unsigned int {
        return std::move(t2)->add_to_sum(_x0);
      };
      return (f1(0u) + f2(0u));
    }();
  }();
};

#endif // INCLUDED_METHOD_PARTIAL_APP
