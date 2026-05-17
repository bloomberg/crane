#ifndef INCLUDED_MEM_SAFETY_PROBE27
#define INCLUDED_MEM_SAFETY_PROBE27

#include <algorithm>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe27 {
  /// Probe 27: Closures capturing whole tree without match.
  ///
  /// Attack vector: Closures stored in data structures that capture
  /// the whole tree parameter (not through a match). Tests whether
  /// Crane creates a proper clone when there's no match destructuring
  /// to trigger the explicit copy mechanism.
  ///
  /// Additional vectors:
  /// - if/else returning closures (Sif at top level, not Smatch)
  /// - closures capturing multiple tree parameters
  /// - closures stored in user-defined inductives
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

  static uint64_t tree_sum(const tree &t);
  static uint64_t tree_depth(const tree &t);
  /// TEST 1: Pair containing closure that captures whole tree.
  /// No match on t — just direct capture. Tests whether Crane
  /// creates a clone of t for the closure.
  static std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
  pair_with_fn(tree t);
  static inline const uint64_t test_pair_with_fn = []() {
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t> p =
        pair_with_fn(tree::node(
            tree::node(tree::leaf(), UINT64_C(3), tree::leaf()), UINT64_C(7),
            tree::node(tree::leaf(), UINT64_C(11), tree::leaf())));
    return (p.first(UINT64_C(100)) + p.second);
  }();
  /// TEST 2: if/else returning different closures in a pair.
  /// After IIFE inlining, this becomes a top-level Sif.
  /// return_captures_by_value may not process inner returns.
  static std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
  cond_pair_fn(tree t, bool b);
  static inline const uint64_t test_cond_pair_fn = []() {
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t> p1 = cond_pair_fn(
        tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                   UINT64_C(7),
                   tree::node(tree::leaf(), UINT64_C(11), tree::leaf())),
        true);
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t> p2 = cond_pair_fn(
        tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                   UINT64_C(7),
                   tree::node(tree::leaf(), UINT64_C(11), tree::leaf())),
        false);
    return (((p1.first(UINT64_C(100)) + p1.second) + p2.first(UINT64_C(200))) +
            p2.second);
  }();
  /// TEST 3: Closure capturing TWO tree parameters.
  static std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
  pair_two_trees(tree t1, tree t2);
  static inline const uint64_t test_pair_two_trees = []() {
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t> p =
        pair_two_trees(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                       tree::node(tree::leaf(), UINT64_C(10), tree::leaf()));
    return (p.first(UINT64_C(100)) + p.second);
  }();
  /// TEST 4: Closure stored in option (no match on tree).
  static std::optional<std::function<uint64_t(uint64_t)>> opt_tree_fn(tree t,
                                                                      bool b);
  static inline const uint64_t test_opt_tree_fn = []() -> uint64_t {
    auto _cs =
        opt_tree_fn(tree::node(tree::leaf(), UINT64_C(15), tree::leaf()), true);
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return f(UINT64_C(100));
    } else {
      return UINT64_C(0);
    }
  }();
  /// TEST 5: Nested closures — inner captures tree, outer captures inner.
  /// Tests that the inner closure correctly clones the tree.
  static std::pair<std::function<uint64_t(uint64_t)>, uint64_t>
  nested_closure_pair(tree t);
  static inline const uint64_t test_nested_closure_pair = []() {
    std::pair<std::function<uint64_t(uint64_t)>, uint64_t> p =
        nested_closure_pair(
            tree::node(tree::leaf(), UINT64_C(5), tree::leaf()));
    return (p.first(UINT64_C(100)) + p.second);
  }();
  /// TEST 6: Three closures stored in a triple, each using tree differently.
  static std::pair<std::pair<std::function<uint64_t(uint64_t)>,
                             std::function<uint64_t(uint64_t)>>,
                   uint64_t>
  triple_fns(tree t);
  static inline const uint64_t test_triple_fns = []() {
    std::pair<std::pair<std::function<uint64_t(uint64_t)>,
                        std::function<uint64_t(uint64_t)>>,
              uint64_t>
        tr = triple_fns(tree::node(
            tree::node(tree::leaf(), UINT64_C(1), tree::leaf()), UINT64_C(2),
            tree::node(tree::leaf(), UINT64_C(3), tree::leaf())));
    return (
        ((tr.first).first(UINT64_C(100)) + (tr.first).second(UINT64_C(200))) +
        tr.second);
  }();
  /// TEST 7: Closure and tree value stored together in a pair.
  /// Tests whether the closure's capture and the tree return
  /// are independent clones.
  static std::pair<std::function<uint64_t(uint64_t)>, tree> fn_and_tree(tree t);
  static inline const uint64_t test_fn_and_tree = []() {
    std::pair<std::function<uint64_t(uint64_t)>, tree> p =
        fn_and_tree(tree::node(tree::leaf(), UINT64_C(7), tree::leaf()));
    return (p.first(UINT64_C(100)) + tree_sum(p.second));
  }();
  /// TEST 8: Closure captures tree, stored in option inside a pair.
  /// Multiple levels of wrapping.
  static std::pair<std::optional<std::function<uint64_t(uint64_t)>>, uint64_t>
  wrapped_fn(tree t, bool b);
  static inline const uint64_t test_wrapped_fn = []() {
    std::pair<std::optional<std::function<uint64_t(uint64_t)>>, uint64_t> p =
        wrapped_fn(
            tree::node(tree::node(tree::leaf(), UINT64_C(2), tree::leaf()),
                       UINT64_C(4),
                       tree::node(tree::leaf(), UINT64_C(6), tree::leaf())),
            true);
    auto _cs = p.first;
    if (_cs.has_value()) {
      const std::function<uint64_t(uint64_t)> &f = *_cs;
      return (f(UINT64_C(100)) + p.second);
    } else {
      return UINT64_C(0);
    }
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE27
