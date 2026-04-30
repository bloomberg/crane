#ifndef INCLUDED_CLOSURE_CHAIN
#define INCLUDED_CLOSURE_CHAIN

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ClosureChain {
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
    tree clone() const {
      tree _out{};

      struct _CloneFrame {
        const tree *_src;
        tree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          _dst->d_v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ =
              Node{_alt.d_a0 ? std::make_unique<tree>() : nullptr, _alt.d_a1,
                   _alt.d_a2 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), std::move(a1),
                       std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.d_v_)) {
          auto &_alt = std::get<Node>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rect<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rect<T1>(f, f0, *(d_a2)));
    }
  }

  template <typename T1, MapsTo<T1, tree, T1, unsigned int, tree, T1> F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rec<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rec<T1>(f, f0, *(d_a2)));
    }
  }

  static unsigned int tree_sum(const tree &t);
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
  static unsigned int make_chain(const unsigned int &n, const tree &t,
                                 unsigned int _x0);
  /// Test: make_chain 0 t 5 = tree_sum(t) + 5 = 10 + 5 = 15
  static inline const unsigned int chain_0 = []() {
    tree t = tree::node(tree::leaf(), 10u, tree::leaf());
    return make_chain(0u, std::move(t), 5u);
  }();
  /// Test: make_chain 1 t 5 = (make_chain 0 t) (5 + 1) = 10 + 6 = 16
  static inline const unsigned int chain_1 = []() {
    tree t = tree::node(tree::leaf(), 10u, tree::leaf());
    return make_chain(1u, std::move(t), 5u);
  }();
  /// Test: make_chain 3 t 0 = (make_chain 0 t) 3 = 10 + 3 = 13
  static inline const unsigned int chain_3 = []() {
    tree t = tree::node(tree::leaf(), 10u, tree::leaf());
    return make_chain(3u, std::move(t), 0u);
  }();
  /// Store the chain result and call it twice.
  /// If make_chain returns a chain with dangling references,
  /// the second call through clobbered stack would give wrong result.
  static inline const unsigned int chain_double_call = []() {
    return []() {
      tree t = tree::node(tree::leaf(), 10u, tree::leaf());
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return make_chain(2u, t, _x0);
      };
      return (f(0u) + f(100u));
    }();
  }();
};

#endif // INCLUDED_CLOSURE_CHAIN
