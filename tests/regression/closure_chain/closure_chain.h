#ifndef INCLUDED_CLOSURE_CHAIN
#define INCLUDED_CLOSURE_CHAIN

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct ClosureChain {
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
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rect<T1>(f, f0, *a0), a1, *a2,
                tree_rect<T1>(f, f0, *a2));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rec<T1>(f, f0, *a0), a1, *a2,
                tree_rec<T1>(f, f0, *a2));
    }
  }

  static uint64_t tree_sum(const tree &t);
  /// Build a chain of closures via recursion.
  /// Each level wraps the previous closure in a new one.
  ///
  /// make_chain 0 t = fun x => tree_sum t + x
  /// make_chain 1 t = fun x => (fun x => tree_sum t + x) (x + 1)
  /// make_chain n t = fun x => (make_chain (n-1) t) (x + 1)
  ///
  /// BUG HYPOTHESIS: make_chain (S n') t creates a local binding
  /// f := make_chain n' t, then returns fun x => f (x + 1).
  /// If f is captured by &, it dies when make_chain returns.
  static uint64_t make_chain(uint64_t n, const tree &t, uint64_t _x0);
  /// Test: make_chain 0 t 5 = tree_sum(t) + 5 = 10 + 5 = 15
  static inline const uint64_t chain_0 = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    return make_chain(UINT64_C(0), std::move(t), UINT64_C(5));
  }();
  /// Test: make_chain 1 t 5 = (make_chain 0 t) (5 + 1) = 10 + 6 = 16
  static inline const uint64_t chain_1 = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    return make_chain(UINT64_C(1), std::move(t), UINT64_C(5));
  }();
  /// Test: make_chain 3 t 0 = (make_chain 0 t) 3 = 10 + 3 = 13
  static inline const uint64_t chain_3 = []() {
    tree t = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
    return make_chain(UINT64_C(3), std::move(t), UINT64_C(0));
  }();
  /// Store the chain result and call it twice.
  /// If make_chain returns a chain with dangling references,
  /// the second call through clobbered stack would give wrong result.
  static inline const uint64_t chain_double_call = []() {
    return []() {
      tree t = tree::node(tree::leaf(), UINT64_C(10), tree::leaf());
      std::function<uint64_t(uint64_t)> f =
          [=](uint64_t _x0) mutable -> uint64_t {
        return make_chain(UINT64_C(2), t, _x0);
      };
      return (f(UINT64_C(0)) + f(UINT64_C(100)));
    }();
  }();
};

#endif // INCLUDED_CLOSURE_CHAIN
