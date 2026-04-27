#ifndef INCLUDED_THIS_CAPTURE_DANGLING
#define INCLUDED_THIS_CAPTURE_DANGLING

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ThisCaptureDangling {
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
            d_a0 ? std::make_unique<ThisCaptureDangling::tree>(d_a0->clone())
                 : nullptr,
            d_a1,
            d_a2 ? std::make_unique<ThisCaptureDangling::tree>(d_a2->clone())
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

    /// BUG HYPOTHESIS: When get_fn is methodified (tree is the only inductive),
    /// the first argument t becomes the raw this pointer.
    ///
    /// The return type is option (nat -> nat) — one branch returns None,
    /// the other returns Some (fun x => x + tree_sum t). The option wrapper
    /// prevents lambda flattening, so the inner lambda IS a genuine C++ lambda.
    ///
    /// The lambda captures this via =, this. Since the return type
    /// does NOT contain shared_ptr<tree>, replace_return_this_stmt is NOT
    /// applied — this stays as a raw pointer. If the closure outlives the
    /// tree's shared_ptr, we have use-after-free.
    ///
    /// Note: option is custom-extracted to std::optional.
    __attribute__((pure))
    std::optional<std::function<unsigned int(unsigned int)>>
    get_fn() const {
      std::shared_ptr<tree> _self = std::make_shared<tree>(*(this));
      auto _cs = (*(this)).tree_sum();
      if (_cs <= 0) {
        return std::optional<std::function<unsigned int(unsigned int)>>();
      } else {
        unsigned int _x = _cs - 1;
        return std::make_optional<std::function<unsigned int(unsigned int)>>(
            [=](const unsigned int &x) mutable {
              return (x + (*(_self)).tree_sum());
            });
      }
    }

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
    __attribute__((pure)) wrapper *operator->() { return this; }

    __attribute__((pure)) const wrapper *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = wrapper(); }

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

  /// test1: Call get_fn on a temporary tree with sum=42.
  /// The tree shared_ptr is released after get_fn returns.
  /// Unwrapping the option and calling the closure dereferences
  /// the dangling this.
  /// Expected: match result is Some f, then f 10 = 10 + 42 = 52.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs = tree::node(tree::leaf(), 42u, tree::leaf()).get_fn();
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(10u);
    } else {
      return 999u;
    }
  }();
  /// test2: Same pattern with a larger tree (sum = 42).
  /// Expected: 5 + 42 = 47.
  static inline const unsigned int test2 = []() -> unsigned int {
    auto _cs = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                          tree::node(tree::leaf(), 12u, tree::leaf()))
                   .get_fn();
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(5u);
    } else {
      return 999u;
    }
  }();
  /// test3: Allocate another tree between getting the closure and calling it.
  /// This increases memory pressure on the freed region.
  /// Expected: f noise = noise + 100 where noise = 1+2+3 = 6. So 106.
  static inline const unsigned int test3 = []() {
    std::optional<std::function<unsigned int(unsigned int)>> opt =
        tree::node(tree::leaf(), 100u, tree::leaf()).get_fn();
    unsigned int noise =
        tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                   tree::node(tree::leaf(), 3u, tree::leaf()))
            .tree_sum();
    if (opt.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *opt;
      return f(noise);
    } else {
      return 999u;
    }
  }();
};

#endif // INCLUDED_THIS_CAPTURE_DANGLING
