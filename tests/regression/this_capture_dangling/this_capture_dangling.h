#ifndef INCLUDED_THIS_CAPTURE_DANGLING
#define INCLUDED_THIS_CAPTURE_DANGLING

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct ThisCaptureDangling {
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
    ~tree() {
      std::vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

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
    std::optional<std::function<uint64_t(uint64_t)>> get_fn() const {
      tree _self_val = *this;
      auto _cs = this->tree_sum();
      if (_cs <= 0) {
        return std::optional<std::function<uint64_t(uint64_t)>>();
      } else {
        uint64_t _x = _cs - 1;
        return std::make_optional<std::function<uint64_t(uint64_t)>>(
            [=](uint64_t x) mutable { return (x + _self_val.tree_sum()); });
      }
    }

    uint64_t tree_sum() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return ((a0->tree_sum() + a1) + a2->tree_sum());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return f0(*a0, a0->template tree_rec<T1>(f, f0), a1, *a2,
                  a2->template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return f0(*a0, a0->template tree_rect<T1>(f, f0), a1, *a2,
                  a2->template tree_rect<T1>(f, f0));
      }
    }
  };

  struct wrapper {
    // DATA
    tree a0;

    // ACCESSORS
    wrapper clone() const { return {a0}; }

    // CREATORS
    static wrapper wrap(tree a0) { return {std::move(a0)}; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, tree &>
  static T1 wrapper_rect(F0 &&f, const wrapper &w) {
    const auto &[a0] = w;
    return f(a0);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, tree &>
  static T1 wrapper_rec(F0 &&f, const wrapper &w) {
    const auto &[a0] = w;
    return f(a0);
  }

  /// test1: Call get_fn on a temporary tree with sum=42.
  /// The tree shared_ptr is released after get_fn returns.
  /// Unwrapping the option and calling the closure dereferences
  /// the dangling this.
  /// Expected: match result is Some f, then f 10 = 10 + 42 = 52.
  static inline const uint64_t test1 = []() -> uint64_t {
    auto _cs = tree::node(tree::leaf(), UINT64_C(42), tree::leaf()).get_fn();
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(10));
    } else {
      return UINT64_C(999);
    }
  }();
  /// test2: Same pattern with a larger tree (sum = 42).
  /// Expected: 5 + 42 = 47.
  static inline const uint64_t test2 = []() -> uint64_t {
    auto _cs = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                          UINT64_C(20),
                          tree::node(tree::leaf(), UINT64_C(12), tree::leaf()))
                   .get_fn();
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(5));
    } else {
      return UINT64_C(999);
    }
  }();
  /// test3: Allocate another tree between getting the closure and calling it.
  /// This increases memory pressure on the freed region.
  /// Expected: f noise = noise + 100 where noise = 1+2+3 = 6. So 106.
  static inline const uint64_t test3 = []() {
    std::optional<std::function<uint64_t(uint64_t)>> opt =
        tree::node(tree::leaf(), UINT64_C(100), tree::leaf()).get_fn();
    uint64_t noise =
        tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                   UINT64_C(2),
                   tree::node(tree::leaf(), UINT64_C(3), tree::leaf()))
            .tree_sum();
    if (opt.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *opt;
      return f(noise);
    } else {
      return UINT64_C(999);
    }
  }();
};

#endif // INCLUDED_THIS_CAPTURE_DANGLING
