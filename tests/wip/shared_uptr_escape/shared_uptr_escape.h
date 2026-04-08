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
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

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

    static std::unique_ptr<tree> leaf_uptr() {
      return std::make_unique<tree>(Leaf{});
    }

    static std::unique_ptr<tree> node_uptr(const std::shared_ptr<tree> &a0,
                                           unsigned int a1,
                                           const std::shared_ptr<tree> &a2) {
      return std::make_unique<tree>(Node{a0, std::move(a1), a2});
    }

    static std::unique_ptr<tree> node_uptr(std::shared_ptr<tree> &&a0,
                                           unsigned int a1,
                                           std::shared_ptr<tree> &&a2) {
      return std::make_unique<tree>(
          Node{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// Pattern 2: Return tree from match, then use it twice.
    /// The match result is a temporary that might be unique_ptr.
    std::shared_ptr<tree> extract_subtree(const unsigned int which) const {
      return std::visit(
          Overloaded{
              [](const typename tree::Leaf _args) -> std::shared_ptr<tree> {
                return tree::leaf();
              },
              [&](const typename tree::Node _args) -> std::shared_ptr<tree> {
                if (which <= 0) {
                  return _args.d_a0;
                } else {
                  unsigned int _x0 = which - 1;
                  return _args.d_a2;
                }
              }},
          this->v());
    }

    /// dup: takes a tree and returns a pair with two references to it.
    /// This REQUIRES the tree to be shared_ptr, since both elements
    /// of the pair point to the same tree.
    __attribute__((pure))
    std::pair<std::shared_ptr<tree>, std::shared_ptr<tree>>
    dup() const {
      return std::make_pair(this, this);
    }

    __attribute__((pure)) unsigned int tree_sum() const {
      return std::visit(
          Overloaded{[](const typename tree::Leaf _args) -> unsigned int {
                       return 0u;
                     },
                     [](const typename tree::Node _args) -> unsigned int {
                       return ((_args.d_a0->tree_sum() + _args.d_a1) +
                               _args.d_a2->tree_sum());
                     }},
          this->v());
    }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    return std::visit(
        Overloaded{[&](const typename tree::Leaf _args) -> T1 { return f; },
                   [&](const typename tree::Node _args) -> T1 {
                     return f0(_args.d_a0, tree_rect<T1>(f, f0, _args.d_a0),
                               _args.d_a1, _args.d_a2,
                               tree_rect<T1>(f, f0, _args.d_a2));
                   }},
        t->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>, T1, unsigned int,
                                std::shared_ptr<tree>, T1>
                             F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const std::shared_ptr<tree> &t) {
    return std::visit(
        Overloaded{[&](const typename tree::Leaf _args) -> T1 { return f; },
                   [&](const typename tree::Node _args) -> T1 {
                     return f0(_args.d_a0, tree_rec<T1>(f, f0, _args.d_a0),
                               _args.d_a1, _args.d_a2,
                               tree_rec<T1>(f, f0, _args.d_a2));
                   }},
        t->v());
  }

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
    std::unique_ptr<tree> t =
        tree::node_uptr(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
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

    static std::unique_ptr<wrapper> wrap_uptr(const std::shared_ptr<tree> &a0) {
      return std::make_unique<wrapper>(Wrap{a0});
    }

    static std::unique_ptr<wrapper> wrap_uptr(std::shared_ptr<tree> &&a0) {
      return std::make_unique<wrapper>(Wrap{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>> F0>
  static T1 wrapper_rect(F0 &&f, const std::shared_ptr<wrapper> &w) {
    return std::visit(Overloaded{[&](const typename wrapper::Wrap _args) -> T1 {
                        return f(_args.d_a0);
                      }},
                      w->v());
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<tree>> F0>
  static T1 wrapper_rec(F0 &&f, const std::shared_ptr<wrapper> &w) {
    return std::visit(Overloaded{[&](const typename wrapper::Wrap _args) -> T1 {
                        return f(_args.d_a0);
                      }},
                      w->v());
  }

  static std::shared_ptr<wrapper> wrap_tree(std::shared_ptr<tree> t);
  static inline const unsigned int unwrap_and_dup = []() {
    std::unique_ptr<tree> t = tree::node_uptr(tree::leaf(), 42u, tree::leaf());
    std::shared_ptr<wrapper> w = wrap_tree(std::move(t));
    return std::visit(
        Overloaded{[](const typename wrapper::Wrap _args) -> unsigned int {
          return (_args.d_a0->tree_sum() + _args.d_a0->tree_sum());
        }},
        w->v());
  }();
};

#endif // INCLUDED_SHARED_UPTR_ESCAPE
