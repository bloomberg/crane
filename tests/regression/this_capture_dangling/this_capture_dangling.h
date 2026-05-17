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
      std::unique_ptr<tree> a0;
      unsigned int a1;
      std::unique_ptr<tree> a2;
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

    tree(const tree &_other) : v_(std::move(_other.clone().v_)) {}

    tree(tree &&_other) noexcept : v_(std::move(_other.v_)) {}

    tree &operator=(const tree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    tree &operator=(tree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    tree clone() const {
      tree _out{};

      struct _CloneFrame {
        const tree *_src;
        tree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          _dst->v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ = Node{_alt.a0 ? std::make_unique<tree>() : nullptr, _alt.a1,
                          _alt.a2 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), a1,
                       std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
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
    std::optional<std::function<unsigned int(unsigned int)>> get_fn() const {
      tree _self_val = *this;
      auto _cs = (*this).tree_sum();
      if (_cs <= 0) {
        return std::optional<std::function<unsigned int(unsigned int)>>();
      } else {
        unsigned int _x = _cs - 1;
        return std::make_optional<std::function<unsigned int(unsigned int)>>(
            [=](unsigned int x) mutable { return (x + _self_val.tree_sum()); });
      }
    }

    unsigned int tree_sum() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return 0u;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return (((*a0).tree_sum() + a1) + (*a2).tree_sum());
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                     tree &, T1 &>
    T1 tree_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return f0(*a0, (*a0).template tree_rec<T1>(f, f0), a1, *a2,
                  (*a2).template tree_rec<T1>(f, f0));
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                     tree &, T1 &>
    T1 tree_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return f;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return f0(*a0, (*a0).template tree_rect<T1>(f, f0), a1, *a2,
                  (*a2).template tree_rect<T1>(f, f0));
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
