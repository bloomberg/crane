#ifndef INCLUDED_CPS_CLOSURE_CHAIN
#define INCLUDED_CPS_CLOSURE_CHAIN

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct CpsClosureChain {
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

  /// CPS-style tree traversal that builds a deep chain of continuations.
  ///
  /// BUG HYPOTHESIS: Each recursive call creates a closure that captures
  /// n (from the pattern match on the current node) and k (the
  /// continuation from the caller). The chain of closures forms a
  /// linked-list-like structure on the heap via std::function copies.
  /// When the chain is finally invoked, each closure needs its captured
  /// n to still be valid.
  ///
  /// Unlike the fixpoint-escape tests in wip/, these are SIMPLE lambdas
  /// (not local fixpoints), so they should use = capture. The question
  /// is whether the = capture correctly copies all pattern variables,
  /// especially when the pattern match is on a shared_ptr type and the
  /// structured bindings are references.
  static uint64_t tree_sum_cps(const tree &t,
                               std::function<uint64_t(uint64_t)> k) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return k(UINT64_C(0));
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      const tree &a0_value = *a0;
      const tree &a2_value = *a2;
      return tree_sum_cps(a0_value, [=](uint64_t left_sum) mutable {
        return tree_sum_cps(a2_value, [=](uint64_t right_sum) mutable {
          return k(((left_sum + a1) + right_sum));
        });
      });
    }
  }

  static uint64_t tree_sum(const tree &t);
  /// Build a deep tree to stress the closure chain.
  static tree build_left(uint64_t n);
  static tree build_right(uint64_t n);
  static tree build_balanced(uint64_t n);
  /// Test: left-spine tree with 5 nodes: sum = 1+2+3+4+5 = 15
  static inline const uint64_t test_left = tree_sum(build_left(UINT64_C(5)));
  /// Test: right-spine tree with 5 nodes: sum = 1+2+3+4+5 = 15
  static inline const uint64_t test_right = tree_sum(build_right(UINT64_C(5)));
  /// Test: balanced tree depth 3: values 1,2,3 with structure
  /// Node (Node (Node Leaf 1 Leaf) 2 (Node Leaf 1 Leaf))
  /// 3
  /// (Node (Node Leaf 1 Leaf) 2 (Node Leaf 1 Leaf))
  /// sum = 4*1 + 2*2 + 1*3 = 11
  static inline const uint64_t test_balanced =
      tree_sum(build_balanced(UINT64_C(3)));

  /// CPS fold: accumulates results through continuation chain.
  /// This creates closures that capture BOTH a pattern variable
  /// AND the accumulator function.
  template <typename F2>
    requires std::is_invocable_r_v<uint64_t, F2 &, uint64_t &, uint64_t &,
                                   uint64_t &>
  static uint64_t tree_fold_cps(const tree &t, uint64_t base, F2 &&combine,
                                std::function<uint64_t(uint64_t)> k) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return k(base);
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      const tree &a0_value = *a0;
      const tree &a2_value = *a2;
      return tree_fold_cps(
          a0_value, base, combine, [=](uint64_t left_result) mutable {
            return tree_fold_cps(
                a2_value, base, combine, [=](uint64_t right_result) mutable {
                  return k(combine(left_result, a1, right_result));
                });
          });
    }
  }

  /// Test: fold with multiplication: each node multiplies (left + right + n)
  static inline const uint64_t test_fold = tree_fold_cps(
      tree::node(tree::node(tree::leaf(), UINT64_C(2), tree::leaf()),
                 UINT64_C(3),
                 tree::node(tree::leaf(), UINT64_C(4), tree::leaf())),
      UINT64_C(1),
      [](uint64_t l, uint64_t n, uint64_t r) { return ((l + n) + r); },
      [](uint64_t x) { return x; });
  /// Store CPS result in a pair with another computation to test
  /// that the continuation chain doesn't interfere with other data.
  static inline const std::pair<uint64_t, uint64_t> test_pair = []() {
    tree t = build_left(UINT64_C(4));
    uint64_t s = tree_sum(t);
    uint64_t f = tree_fold_cps(
        std::move(t), UINT64_C(0),
        [](uint64_t l, uint64_t n, uint64_t r) { return ((l + n) + r); },
        [](uint64_t x) { return x; });
    return std::make_pair(s, f);
  }();
};

#endif // INCLUDED_CPS_CLOSURE_CHAIN
