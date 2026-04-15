#ifndef INCLUDED_REUSE_SCRUTINEE
#define INCLUDED_REUSE_SCRUTINEE

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

struct ReuseScrutinee {
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
      const auto &_m = *std::get_if<typename tree::Node>(&t->v());
      return f0(_m.d_a0, tree_rect<T1>(f, f0, _m.d_a0), _m.d_a1, _m.d_a2,
                tree_rect<T1>(f, f0, _m.d_a2));
    }
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    if (std::holds_alternative<typename tree::Leaf>(t->v())) {
      return f;
    } else {
      const auto &_m = *std::get_if<typename tree::Node>(&t->v());
      return f0(_m.d_a0, tree_rec<T1>(f, f0, _m.d_a0), _m.d_a1, _m.d_a2,
                tree_rec<T1>(f, f0, _m.d_a2));
    }
  }

  /// Extract the value from the left subtree.
  /// This accesses the Node's d_a0 field (left subtree).
  __attribute__((pure)) static unsigned int
  left_val(const std::shared_ptr<tree> &t);
  /// Extract the value from the right subtree.
  __attribute__((pure)) static unsigned int
  right_val(const std::shared_ptr<tree> &t);
  /// Sum of left and right subtree values.
  __attribute__((pure)) static unsigned int
  subtree_sum(const std::shared_ptr<tree> &t);
  /// REUSE BUG TRIGGER:
  /// The match on t returns Node Leaf (subtree_sum t) Leaf.
  /// If the reuse optimization fires (t.use_count() == 1):
  /// 1. Fields are moved out: l = move(d_a0), r = move(d_a2)
  /// → d_a0 and d_a2 are now null
  /// 2. New values are computed: subtree_sum(t) accesses t's subtrees
  /// → t's d_a0 is null → left_val dereferences null → CRASH
  static inline const unsigned int reuse_bug = []() {
    std::shared_ptr<tree> t =
        tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                   tree::node(tree::leaf(), 30u, tree::leaf()));
    if (std::holds_alternative<typename tree::Leaf>(t->v())) {
      return 0u;
    } else {
      return subtree_sum(std::move(t));
    }
  }();
  /// Direct version: the result directly uses the scrutinee in a
  /// tail constructor that could trigger reuse.
  static inline const std::shared_ptr<tree> reuse_direct = []() {
    std::shared_ptr<tree> t =
        tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                   tree::node(tree::leaf(), 30u, tree::leaf()));
    if (std::holds_alternative<typename tree::Leaf>(t->v()) &&
        t.use_count() == 1) {
      return t;
    } else if (std::holds_alternative<typename tree::Leaf>(t->v())) {
      return tree::leaf();
    } else {
      const auto &_m = *std::get_if<typename tree::Node>(&t->v());
      return tree::node(tree::leaf(), subtree_sum(t), _m.d_a2);
    }
  }();
  /// Expected: subtree_sum on Node(Node(Leaf,10,Leaf), 20, Node(Leaf,30,Leaf))
  /// = left_val + right_val = 10 + 30 = 40
  static inline const unsigned int expected_sum =
      subtree_sum(tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                             tree::node(tree::leaf(), 30u, tree::leaf())));
};

#endif // INCLUDED_REUSE_SCRUTINEE
