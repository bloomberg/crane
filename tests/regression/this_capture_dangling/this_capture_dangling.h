#ifndef INCLUDED_THIS_CAPTURE_DANGLING
#define INCLUDED_THIS_CAPTURE_DANGLING

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct ThisCaptureDangling {
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
      std::shared_ptr<tree> _self =
          std::const_pointer_cast<tree>(this->shared_from_this());
      auto _cs = this->tree_sum();
      if (_cs <= 0) {
        return std::optional<std::function<unsigned int(unsigned int)>>();
      } else {
        unsigned int _x = _cs - 1;
        return std::make_optional<std::function<unsigned int(unsigned int)>>(
            [=](const unsigned int x) mutable {
              return (x + _self->tree_sum());
            });
      }
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

  /// test1: Call get_fn on a temporary tree with sum=42.
  /// The tree shared_ptr is released after get_fn returns.
  /// Unwrapping the option and calling the closure dereferences
  /// the dangling this.
  /// Expected: match result is Some f, then f 10 = 10 + 42 = 52.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs = tree::node(tree::leaf(), 42u, tree::leaf())->get_fn();
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
                   ->get_fn();
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
        tree::node(tree::leaf(), 100u, tree::leaf())->get_fn();
    unsigned int noise =
        tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                   tree::node(tree::leaf(), 3u, tree::leaf()))
            ->tree_sum();
    if (opt.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *opt;
      return f(noise);
    } else {
      return 999u;
    }
  }();
};

#endif // INCLUDED_THIS_CAPTURE_DANGLING
