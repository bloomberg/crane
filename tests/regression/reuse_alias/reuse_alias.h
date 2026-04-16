#ifndef INCLUDED_REUSE_ALIAS
#define INCLUDED_REUSE_ALIAS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct ReuseAlias {
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

  __attribute__((pure)) static unsigned int
  tree_sum(const std::shared_ptr<tree> &t);
  static std::shared_ptr<tree> transform_tree(const std::shared_ptr<tree> &t);
  static inline const unsigned int reuse_fn_bug = []() {
    std::shared_ptr<tree> t =
        tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                   tree::node(tree::leaf(), 30u, tree::leaf()));
    return tree_sum(transform_tree(std::move(t)));
  }();
  static std::shared_ptr<tree>
  nested_match_reuse(const std::shared_ptr<tree> &t, const unsigned int flag);
  static inline const unsigned int nested_reuse_bug = []() {
    std::shared_ptr<tree> t =
        tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                   tree::node(tree::leaf(), 30u, tree::leaf()));
    return (tree_sum(nested_match_reuse(t, 0u)) +
            tree_sum(nested_match_reuse(t, 1u)));
  }();
  static std::shared_ptr<tree> annotate_sum(const std::shared_ptr<tree> &t);
  static inline const unsigned int recursive_reuse_bug = []() {
    std::shared_ptr<tree> t =
        tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                   tree::node(tree::leaf(), 30u, tree::leaf()));
    return tree_sum(annotate_sum(std::move(t)));
  }();
};

#endif // INCLUDED_REUSE_ALIAS
