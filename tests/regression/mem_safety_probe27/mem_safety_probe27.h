#ifndef INCLUDED_MEM_SAFETY_PROBE27
#define INCLUDED_MEM_SAFETY_PROBE27

#include "crane_fn.h"
#include "fn.h"
#include "small_vector.h"
#include <algorithm>
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

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
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    tree(const tree &) = default;
    tree &operator=(const tree &) = default;
    tree(tree &&) = default;
    tree &operator=(tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 tree_rect(T1 f, F1 &&f0,
                      const tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

    struct CraneEnter {
      const tree *t;
    };

    /// CraneCont_Node: saves [a0, a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Node {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      const tree *a2;
    };

    /// CraneCont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive
    /// call, then processes rest.
    struct CraneCont_Node_1 {
      T1 _tmp2;
      std::shared_ptr<tree> a0;
      uint64_t a1;
      const tree *a2;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&t});
    /// Loopified tree_rect: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(CraneCont_Node{a0, a1, crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Node>(_frame));
        std::shared_ptr<tree> a0 = std::move(_f.a0);
        uint64_t a1 = _f.a1;
        const tree &a2 = *_f.a2;
        _stack.emplace_back(
            CraneCont_Node_1{std::move(_result), std::move(a0), a1, &a2});
        _stack.emplace_back(CraneEnter{&a2});
      } else {
        auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
        std::shared_ptr<tree> a0 = std::move(_f.a0);
        uint64_t a1 = _f.a1;
        const tree &a2 = *_f.a2;
        _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1 tree_rec(const T1 &f, F1 &&f0, const tree &t) {
    return tree_rect<T1>(f, f0, t);
  }

  static uint64_t tree_sum(const tree &t);
  static uint64_t tree_depth(const tree &t);
  /// TEST 1: Pair containing closure that captures whole tree.
  /// No match on t — just direct capture. Tests whether Crane
  /// creates a clone of t for the closure.
  static std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t>
  pair_with_fn(tree t);
  static inline const uint64_t test_pair_with_fn = []() {
    std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t> p =
        pair_with_fn(tree::node(
            tree::node(tree::leaf(), UINT64_C(3), tree::leaf()), UINT64_C(7),
            tree::node(tree::leaf(), UINT64_C(11), tree::leaf())));
    return (p.first(UINT64_C(100)) + p.second);
  }();
  /// TEST 2: if/else returning different closures in a pair.
  /// After IIFE inlining, this becomes a top-level Sif.
  /// return_captures_by_value may not process inner returns.
  static std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t>
  cond_pair_fn(tree t, bool b);
  static inline const uint64_t test_cond_pair_fn = []() {
    std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t> p1 = cond_pair_fn(
        tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                   UINT64_C(7),
                   tree::node(tree::leaf(), UINT64_C(11), tree::leaf())),
        true);
    std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t> p2 = cond_pair_fn(
        tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                   UINT64_C(7),
                   tree::node(tree::leaf(), UINT64_C(11), tree::leaf())),
        false);
    return (((p1.first(UINT64_C(100)) + p1.second) + p2.first(UINT64_C(200))) +
            p2.second);
  }();
  /// TEST 3: Closure capturing TWO tree parameters.
  static std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t>
  pair_two_trees(tree t1, tree t2);
  static inline const uint64_t test_pair_two_trees = []() {
    std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t> p =
        pair_two_trees(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                       tree::node(tree::leaf(), UINT64_C(10), tree::leaf()));
    return (p.first(UINT64_C(100)) + p.second);
  }();
  /// TEST 4: Closure stored in option (no match on tree).
  static std::optional<crane::fn<uint64_t(uint64_t)>> opt_tree_fn(tree t,
                                                                  bool b);
  static constexpr uint64_t test_opt_tree_fn = UINT64_C(115);
  /// TEST 5: Nested closures — inner captures tree, outer captures inner.
  /// Tests that the inner closure correctly clones the tree.
  static std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t>
  nested_closure_pair(tree t);
  static inline const uint64_t test_nested_closure_pair = []() {
    std::pair<crane::fn<uint64_t(uint64_t)>, uint64_t> p = nested_closure_pair(
        tree::node(tree::leaf(), UINT64_C(5), tree::leaf()));
    return (p.first(UINT64_C(100)) + p.second);
  }();
  /// TEST 6: Three closures stored in a triple, each using tree differently.
  static std::pair<
      std::pair<crane::fn<uint64_t(uint64_t)>, crane::fn<uint64_t(uint64_t)>>,
      uint64_t>
  triple_fns(tree t);
  static inline const uint64_t test_triple_fns = []() {
    std::pair<
        std::pair<crane::fn<uint64_t(uint64_t)>, crane::fn<uint64_t(uint64_t)>>,
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
  static std::pair<crane::fn<uint64_t(uint64_t)>, tree> fn_and_tree(tree t);
  static inline const uint64_t test_fn_and_tree = []() {
    std::pair<crane::fn<uint64_t(uint64_t)>, tree> p =
        fn_and_tree(tree::node(tree::leaf(), UINT64_C(7), tree::leaf()));
    return (p.first(UINT64_C(100)) + tree_sum(p.second));
  }();
  /// TEST 8: Closure captures tree, stored in option inside a pair.
  /// Multiple levels of wrapping.
  static std::pair<std::optional<crane::fn<uint64_t(uint64_t)>>, uint64_t>
  wrapped_fn(tree t, bool b);

  static inline const uint64_t test_wrapped_fn = []() {
    std::pair<std::optional<crane::fn<uint64_t(uint64_t)>>, uint64_t> p =
        wrapped_fn(
            tree::node(tree::node(tree::leaf(), UINT64_C(2), tree::leaf()),
                       UINT64_C(4),
                       tree::node(tree::leaf(), UINT64_C(6), tree::leaf())),
            true);
    auto _cs = p.first;
    if (_cs.has_value()) {
      const crane::fn<uint64_t(uint64_t)> &f = *_cs;
      return (f(UINT64_C(100)) + std::move(p).second);
    } else {
      return UINT64_C(0);
    }
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE27
