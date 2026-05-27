#ifndef INCLUDED_OPTION_CLOSURE_ESCAPE
#define INCLUDED_OPTION_CLOSURE_ESCAPE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct OptionClosureEscape {
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
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rect<T1>(f, f0, *a0), a1, *a2,
                tree_rect<T1>(f, f0, *a2));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rec<T1>(f, f0, *a0), a1, *a2,
                tree_rec<T1>(f, f0, *a2));
    }
  }

  static uint64_t sum_values(const tree &t, uint64_t x);
  /// BUG: pair_escape stores a & lambda in a pair.
  /// The lambda captures parameter t by reference.
  /// When pair_escape returns, t is destroyed → dangling.
  static std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
  pair_escape(tree t);
  /// Call pair_escape, then call it again to clobber the stack,
  /// then use the first result's closure.
  static inline const uint64_t bug_pair_clobber = []() {
    tree t1 = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                         UINT64_C(20),
                         tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t> p1 =
        pair_escape(std::move(t1));
    return std::move(p1).first(UINT64_C(0));
  }();
  /// BUG: match_pair — & captures _args from visit scope.
  static std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
  match_pair(const tree &t);
  static inline const uint64_t bug_match_pair_clobber = []() {
    tree t1 = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                         UINT64_C(20),
                         tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t> p1 =
        match_pair(std::move(t1));
    return std::move(p1).first(UINT64_C(0));
  }();
};

#endif // INCLUDED_OPTION_CLOSURE_ESCAPE
