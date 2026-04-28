#ifndef INCLUDED_SHARED_UPTR_ESCAPE
#define INCLUDED_SHARED_UPTR_ESCAPE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct SharedUptrEscape {
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
            Node{d_a0 ? std::make_unique<SharedUptrEscape::tree>(d_a0->clone())
                      : nullptr,
                 d_a1,
                 d_a2 ? std::make_unique<SharedUptrEscape::tree>(d_a2->clone())
                      : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static tree leaf() { return tree(Leaf{}); }

    __attribute__((pure)) static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), std::move(a1),
                       std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// Pattern 2: Return tree from match, then use it twice.
    /// The match result is a temporary that might be unique_ptr.
    __attribute__((pure)) tree
    extract_subtree(const unsigned int &which) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return tree::leaf();
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        if (which <= 0) {
          return *(d_a0);
        } else {
          unsigned int _x0 = which - 1;
          return *(d_a2);
        }
      }
    }

    /// dup: takes a tree and returns a pair with two references to it.
    /// This REQUIRES the tree to be shared_ptr, since both elements
    /// of the pair point to the same tree.
    __attribute__((pure)) std::pair<tree, tree> dup() const {
      return std::make_pair(*(this), *(this));
    }

    /// identity: takes a tree and returns it unchanged.
    /// The tree enters as owned and leaves as owned.
    __attribute__((pure)) tree identity() const { return std::move(*(this)); }

    __attribute__((pure)) unsigned int tree_sum() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return 0u;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return (((*(d_a0)).tree_sum() + d_a1) + (*(d_a2)).tree_sum());
      }
    }

    template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
    T1 tree_rec(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template tree_rec<T1>(f, f0), d_a1,
                  *(d_a2), (*(d_a2)).template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
    T1 tree_rect(const T1 f, F1 &&f0) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return f;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template tree_rect<T1>(f, f0), d_a1,
                  *(d_a2), (*(d_a2)).template tree_rect<T1>(f, f0));
      }
    }
  };

  /// BUG: Build a tree, then conditionally either return it once
  /// (unique_ptr sufficient) or duplicate it (needs shared_ptr).
  /// If escape analysis optimistically picks unique_ptr based on
  /// one branch, the other branch's sharing crashes.
  __attribute__((pure)) static unsigned int
  conditional_share(const unsigned int &flag);
  static inline const unsigned int use_extracted_twice = []() {
    tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                        tree::node(tree::leaf(), 30u, tree::leaf()));
    tree sub = std::move(t).extract_subtree(0u);
    return (sub.tree_sum() + sub.tree_sum());
  }();

  /// Pattern 3: Build a value, pass to a function that returns it
  /// wrapped in a constructor, then unwrap and use twice.
  struct wrapper {
    // TYPES
    struct Wrap {
      tree d_a0;
    };

    using variant_t = std::variant<Wrap>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    wrapper() {}

    explicit wrapper(Wrap _v) : d_v_(std::move(_v)) {}

    wrapper(const wrapper &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    wrapper(wrapper &&_other) : d_v_(std::move(_other.d_v_)) {}

    wrapper &operator=(const wrapper &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    wrapper &operator=(wrapper &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) wrapper clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<Wrap>(_sv.v());
      return wrapper(Wrap{d_a0.clone()});
    }

    // CREATORS
    __attribute__((pure)) static wrapper wrap(tree a0) {
      return wrapper(Wrap{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, tree> F0>
  static T1 wrapper_rect(F0 &&f, const wrapper &w) {
    const auto &[d_a0] = std::get<typename wrapper::Wrap>(w.v());
    return f(d_a0);
  }

  template <typename T1, MapsTo<T1, tree> F0>
  static T1 wrapper_rec(F0 &&f, const wrapper &w) {
    const auto &[d_a0] = std::get<typename wrapper::Wrap>(w.v());
    return f(d_a0);
  }

  __attribute__((pure)) static wrapper wrap_tree(tree t);
  static inline const unsigned int unwrap_and_dup = []() {
    tree t = tree::node(tree::leaf(), 42u, tree::leaf());
    wrapper w = wrap_tree(std::move(t));
    const auto &[d_a0] = std::get<typename wrapper::Wrap>(w.v());
    return (d_a0.tree_sum() + d_a0.tree_sum());
  }();
};

#endif // INCLUDED_SHARED_UPTR_ESCAPE
