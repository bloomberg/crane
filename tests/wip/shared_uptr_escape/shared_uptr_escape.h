#ifndef INCLUDED_SHARED_UPTR_ESCAPE
#define INCLUDED_SHARED_UPTR_ESCAPE

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

struct SharedUptrEscape {
  struct tree : public std::enable_shared_from_this<tree> {
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

    /// Pattern 2: Return tree from match, then use it twice.
    /// The match result is a temporary that might be unique_ptr.
    std::shared_ptr<tree> extract_subtree(const unsigned int which) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return tree::leaf();
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename tree::Node>(this->v());
        if (which <= 0) {
          return d_a0;
        } else {
          unsigned int _x0 = which - 1;
          return d_a2;
        }
      }
    }

    /// dup: takes a tree and returns a pair with two references to it.
    /// This REQUIRES the tree to be shared_ptr, since both elements
    /// of the pair point to the same tree.
    __attribute__((pure))
    std::pair<std::shared_ptr<tree>, std::shared_ptr<tree>>
    dup() const {
      return std::make_pair(
          std::const_pointer_cast<tree>(this->shared_from_this()),
          std::const_pointer_cast<tree>(this->shared_from_this()));
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

  /// identity: takes a tree and returns it unchanged.
  /// The tree enters as owned and leaves as owned.
  static std::shared_ptr<tree> identity(std::shared_ptr<tree> t);
  /// BUG: Build a tree, then conditionally either return it once
  /// (unique_ptr sufficient) or duplicate it (needs shared_ptr).
  /// If escape analysis optimistically picks unique_ptr based on
  /// one branch, the other branch's sharing crashes.
  __attribute__((pure)) static unsigned int
  conditional_share(const unsigned int flag);
  static inline const unsigned int use_extracted_twice = []() {
    std::shared_ptr<tree> t =
        tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                   tree::node(tree::leaf(), 30u, tree::leaf()));
    std::shared_ptr<tree> sub = std::move(t)->extract_subtree(0u);
    return (sub->tree_sum() + sub->tree_sum());
  }();

  /// Pattern 3: Build a value, pass to a function that returns it
  /// wrapped in a constructor, then unwrap and use twice.
  struct wrapper {
    // TYPES
    struct Wrap {
      std::shared_ptr<tree> d_a0;
    };

    using variant_t = std::variant<Wrap>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit wrapper(Wrap _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<wrapper> wrap(const std::shared_ptr<tree> &a0) {
      return std::make_shared<wrapper>(Wrap{a0});
    }

    static std::shared_ptr<wrapper> wrap(std::shared_ptr<tree> &&a0) {
      return std::make_shared<wrapper>(Wrap{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>> F0>
  static T1 wrapper_rect(F0 &&f, const std::shared_ptr<wrapper> &w) {
    const auto &[d_a0] = std::get<typename wrapper::Wrap>(w->v());
    return f(d_a0);
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>> F0>
  static T1 wrapper_rec(F0 &&f, const std::shared_ptr<wrapper> &w) {
    const auto &[d_a0] = std::get<typename wrapper::Wrap>(w->v());
    return f(d_a0);
  }

  static std::shared_ptr<wrapper> wrap_tree(std::shared_ptr<tree> t);
  static inline const unsigned int unwrap_and_dup = []() {
    std::shared_ptr<tree> t = tree::node(tree::leaf(), 42u, tree::leaf());
    std::shared_ptr<wrapper> w = wrap_tree(std::move(t));
    const auto &[d_a0] = std::get<typename wrapper::Wrap>(w->v());
    return (d_a0->tree_sum() + d_a0->tree_sum());
  }();
};

#endif // INCLUDED_SHARED_UPTR_ESCAPE
