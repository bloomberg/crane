#ifndef INCLUDED_REUSE_SCRUTINEE
#define INCLUDED_REUSE_SCRUTINEE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ReuseScrutinee {
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

    tree &operator=(const tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    tree &operator=(tree &&_other) {
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
            Node{d_a0 ? std::make_unique<ReuseScrutinee::tree>(d_a0->clone())
                      : nullptr,
                 d_a1,
                 d_a2 ? std::make_unique<ReuseScrutinee::tree>(d_a2->clone())
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
    inline variant_t &v_mut() { return d_v_; }

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

  /// Extract the value from the left subtree.
  /// This accesses the Node's d_a0 field (left subtree).
  __attribute__((pure)) static unsigned int left_val(const tree &t);
  /// Extract the value from the right subtree.
  __attribute__((pure)) static unsigned int right_val(const tree &t);
  /// Sum of left and right subtree values.
  __attribute__((pure)) static unsigned int subtree_sum(const tree &t);
  /// REUSE BUG TRIGGER:
  /// The match on t returns Node Leaf (subtree_sum t) Leaf.
  /// If the reuse optimization fires (t.use_count() == 1):
  /// 1. Fields are moved out: l = move(d_a0), r = move(d_a2)
  /// → d_a0 and d_a2 are now null
  /// 2. New values are computed: subtree_sum(t) accesses t's subtrees
  /// → t's d_a0 is null → left_val dereferences null → CRASH
  static inline const unsigned int reuse_bug = []() {
    tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                        tree::node(tree::leaf(), 30u, tree::leaf()));
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return 0u;
    } else {
      return subtree_sum(t);
    }
  }();
  /// Direct version: the result directly uses the scrutinee in a
  /// tail constructor that could trigger reuse.
  static inline const tree reuse_direct = []() {
    tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                        tree::node(tree::leaf(), 30u, tree::leaf()));
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return tree::leaf();
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return tree::node(tree::leaf(), subtree_sum(t), *(d_a2));
    }
  }();
  /// Expected: subtree_sum on Node(Node(Leaf,10,Leaf), 20, Node(Leaf,30,Leaf))
  /// = left_val + right_val = 10 + 30 = 40
  static inline const unsigned int expected_sum =
      subtree_sum(tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                             tree::node(tree::leaf(), 30u, tree::leaf())));
};

#endif // INCLUDED_REUSE_SCRUTINEE
