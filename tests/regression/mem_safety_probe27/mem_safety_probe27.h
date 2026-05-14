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
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          _dst->d_v_ = Leaf();
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ =
              Node(_alt.d_a0 ? std::make_unique<tree>() : nullptr, _alt.d_a1,
                   _alt.d_a2 ? std::make_unique<tree>() : nullptr);
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
    static tree leaf() { return tree(Leaf()); }

    static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node(std::make_unique<tree>(std::move(a0)), std::move(a1),
                       std::make_unique<tree>(std::move(a2))));
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      _stack.reserve(8);
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

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                   tree &, T1 &>
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rect<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rect<T1>(f, f0, *(d_a2)));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                   tree &, T1 &>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rec<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rec<T1>(f, f0, *(d_a2)));
    }
  }

  static unsigned int tree_sum(const tree &t);
  static unsigned int tree_depth(const tree &t);
  /// TEST 1: Pair containing closure that captures whole tree.
  /// No match on t — just direct capture. Tests whether Crane
  /// creates a clone of t for the closure.
  static std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
  pair_with_fn(tree t);
  static inline const unsigned int test_pair_with_fn = []() {
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int> p =
        pair_with_fn(tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                                tree::node(tree::leaf(), 11u, tree::leaf())));
    return (p.first(100u) + p.second);
  }();
  /// TEST 2: if/else returning different closures in a pair.
  /// After IIFE inlining, this becomes a top-level Sif.
  /// return_captures_by_value may not process inner returns.
  static std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
  cond_pair_fn(tree t, const bool b);
  static inline const unsigned int test_cond_pair_fn = []() {
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int> p1 =
        cond_pair_fn(tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                                tree::node(tree::leaf(), 11u, tree::leaf())),
                     true);
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int> p2 =
        cond_pair_fn(tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                                tree::node(tree::leaf(), 11u, tree::leaf())),
                     false);
    return (((p1.first(100u) + p1.second) + p2.first(200u)) + p2.second);
  }();
  /// TEST 3: Closure capturing TWO tree parameters.
  static std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
  pair_two_trees(tree t1, tree t2);
  static inline const unsigned int test_pair_two_trees = []() {
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int> p =
        pair_two_trees(tree::node(tree::leaf(), 5u, tree::leaf()),
                       tree::node(tree::leaf(), 10u, tree::leaf()));
    return (p.first(100u) + p.second);
  }();
  /// TEST 4: Closure stored in option (no match on tree).
  static std::optional<std::function<unsigned int(unsigned int)>>
  opt_tree_fn(tree t, const bool b);
  static inline const unsigned int test_opt_tree_fn = []() -> unsigned int {
    auto _cs = opt_tree_fn(tree::node(tree::leaf(), 15u, tree::leaf()), true);
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(100u);
    } else {
      return 0u;
    }
  }();
  /// TEST 5: Nested closures — inner captures tree, outer captures inner.
  /// Tests that the inner closure correctly clones the tree.
  static std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
  nested_closure_pair(tree t);
  static inline const unsigned int test_nested_closure_pair = []() {
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int> p =
        nested_closure_pair(tree::node(tree::leaf(), 5u, tree::leaf()));
    return (p.first(100u) + p.second);
  }();
  /// TEST 6: Three closures stored in a triple, each using tree differently.
  static std::pair<std::pair<std::function<unsigned int(unsigned int)>,
                             std::function<unsigned int(unsigned int)>>,
                   unsigned int>
  triple_fns(tree t);
  static inline const unsigned int test_triple_fns = []() {
    std::pair<std::pair<std::function<unsigned int(unsigned int)>,
                        std::function<unsigned int(unsigned int)>>,
              unsigned int>
        tr = triple_fns(tree::node(tree::node(tree::leaf(), 1u, tree::leaf()),
                                   2u,
                                   tree::node(tree::leaf(), 3u, tree::leaf())));
    return (((tr.first).first(100u) + (tr.first).second(200u)) + tr.second);
  }();
  /// TEST 7: Closure and tree value stored together in a pair.
  /// Tests whether the closure's capture and the tree return
  /// are independent clones.
  static std::pair<std::function<unsigned int(unsigned int)>, tree>
  fn_and_tree(tree t);
  static inline const unsigned int test_fn_and_tree = []() {
    std::pair<std::function<unsigned int(unsigned int)>, tree> p =
        fn_and_tree(tree::node(tree::leaf(), 7u, tree::leaf()));
    return (p.first(100u) + tree_sum(p.second));
  }();
  /// TEST 8: Closure captures tree, stored in option inside a pair.
  /// Multiple levels of wrapping.
  static std::pair<std::optional<std::function<unsigned int(unsigned int)>>,
                   unsigned int>
  wrapped_fn(tree t, const bool b);
  static inline const unsigned int test_wrapped_fn = []() {
    std::pair<std::optional<std::function<unsigned int(unsigned int)>>,
              unsigned int>
        p = wrapped_fn(tree::node(tree::node(tree::leaf(), 2u, tree::leaf()),
                                  4u,
                                  tree::node(tree::leaf(), 6u, tree::leaf())),
                       true);
    auto _cs = p.first;
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return (f(100u) + p.second);
    } else {
      return 0u;
    }
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE27
