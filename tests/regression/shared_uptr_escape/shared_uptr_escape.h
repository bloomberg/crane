#ifndef INCLUDED_SHARED_UPTR_ESCAPE
#define INCLUDED_SHARED_UPTR_ESCAPE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct SharedUptrEscape {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree> a0;
      uint64_t a1;
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

    static tree node(tree a0, uint64_t a1, tree a2) {
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

    /// Pattern 2: Return tree from match, then use it twice.
    /// The match result is a temporary that might be unique_ptr.
    tree extract_subtree(uint64_t which) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return tree::leaf();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        if (which <= 0) {
          return *a0;
        } else {
          uint64_t _x0 = which - 1;
          return *a2;
        }
      }
    }

    /// dup: takes a tree and returns a pair with two references to it.
    /// This REQUIRES the tree to be shared_ptr, since both elements
    /// of the pair point to the same tree.
    std::pair<tree, tree> dup() const { return std::make_pair(*this, *this); }

    /// identity: takes a tree and returns it unchanged.
    /// The tree enters as owned and leaves as owned.
    tree identity() const { return std::move(*this); }

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

  /// BUG: Build a tree, then conditionally either return it once
  /// (unique_ptr sufficient) or duplicate it (needs shared_ptr).
  /// If escape analysis optimistically picks unique_ptr based on
  /// one branch, the other branch's sharing crashes.
  static uint64_t conditional_share(uint64_t flag);
  static inline const uint64_t use_extracted_twice = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    tree sub = std::move(t).extract_subtree(UINT64_C(0));
    return (sub.tree_sum() + sub.tree_sum());
  }();

  /// Pattern 3: Build a value, pass to a function that returns it
  /// wrapped in a constructor, then unwrap and use twice.
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

  static wrapper wrap_tree(tree t);
  static inline const uint64_t unwrap_and_dup = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(42), tree::leaf());
    wrapper w = wrap_tree(std::move(t));
    auto &[a0] = w;
    return (a0.tree_sum() + a0.tree_sum());
  }();
};

#endif // INCLUDED_SHARED_UPTR_ESCAPE
