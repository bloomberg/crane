#ifndef INCLUDED_MATCH_CLOSURE_ESCAPE
#define INCLUDED_MATCH_CLOSURE_ESCAPE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct MatchClosureEscape {
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
        return tree(Node{
            d_a0 ? std::make_unique<MatchClosureEscape::tree>(d_a0->clone())
                 : nullptr,
            d_a1,
            d_a2 ? std::make_unique<MatchClosureEscape::tree>(d_a2->clone())
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

    __attribute__((pure)) unsigned int sum_values(unsigned int x) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
        return x;
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(_sv.v());
        auto &&_sv0 = *(d_a0);
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return (d_a1 + x);
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename tree::Node>(_sv0.v());
          auto &&_sv1 = *(d_a2);
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            return (d_a10 + x);
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename tree::Node>(_sv1.v());
            return (((d_a10 + d_a11) + d_a1) + x);
          }
        }
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

  /// A box for closures, forces the closure to be stored on the heap.
  struct fn_box {
    // TYPES
    struct Box {
      std::function<unsigned int(unsigned int)> d_a0;
    };

    using variant_t = std::variant<Box>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    fn_box() {}

    explicit fn_box(Box _v) : d_v_(std::move(_v)) {}

    fn_box(const fn_box &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    fn_box(fn_box &&_other) : d_v_(std::move(_other.d_v_)) {}

    fn_box &operator=(const fn_box &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    fn_box &operator=(fn_box &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) fn_box clone() const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<Box>(_sv.v());
      return fn_box(Box{d_a0});
    }

    // CREATORS
    __attribute__((pure)) static fn_box
    box(std::function<unsigned int(unsigned int)> a0) {
      return fn_box(Box{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) fn_box *operator->() { return this; }

    __attribute__((pure)) const fn_box *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = fn_box(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int apply_box(const unsigned int &x) const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<typename fn_box::Box>(_sv.v());
      return d_a0(x);
    }

    template <typename T1,
              MapsTo<T1, std::function<unsigned int(unsigned int)>> F0>
    T1 fn_box_rec(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<typename fn_box::Box>(_sv.v());
      return f(d_a0);
    }

    template <typename T1,
              MapsTo<T1, std::function<unsigned int(unsigned int)>> F0>
    T1 fn_box_rect(F0 &&f) const {
      auto &&_sv = *(this);
      const auto &[d_a0] = std::get<typename fn_box::Box>(_sv.v());
      return f(d_a0);
    }
  };

  /// BUG TRIGGER: match_arm_box
  /// The partial application sum_values l inside a match arm creates a
  /// & lambda capturing the match-bound variable _args (from std::visit).
  /// This lambda is stored in a Box constructor argument.
  /// return_captures_by_value does NOT handle lambdas inside constructor args.
  /// When the visit lambda returns, _args goes out of scope, and the Box
  /// holds a dangling reference to a destroyed shared_ptr.
  __attribute__((pure)) static fn_box match_arm_box(const tree &t);
  /// Use a top-level definition to get a shared_ptr (not unique_ptr).
  static inline const tree test_tree =
      tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                 tree::node(tree::leaf(), 30u, tree::leaf()));
  static inline const unsigned int bug_match_box =
      match_arm_box(test_tree).apply_box(99u);
};

#endif // INCLUDED_MATCH_CLOSURE_ESCAPE
