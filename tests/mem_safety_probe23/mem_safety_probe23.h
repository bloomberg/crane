#ifndef INCLUDED_MEM_SAFETY_PROBE23
#define INCLUDED_MEM_SAFETY_PROBE23

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct MemSafetyProbe23 {
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
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    tree(const tree &) = default;
    tree &operator=(const tree &) = default;
    tree(tree &&) noexcept = default;
    tree &operator=(tree &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rect(T1 f, F1 &&f0,
                      const tree &t) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

    struct _Enter {
      const tree *t;
    };

    /// _After_Node: saves [a0_0, a2, a1, a0_1], dispatches next recursive call.
    struct _After_Node {
      const tree *a0_0;
      tree a2;
      uint64_t a1;
      tree a0_1;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      std::decay_t<T1> _result;
      tree a2;
      uint64_t a1;
      tree a0;
    };

    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_rect: _Enter -> _After_Node -> _Combine_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(_After_Node{crane_raw(a0), *a2, a1, *a0});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        }
      } else if (std::holds_alternative<_After_Node>(_frame)) {
        auto _f = std::move(std::get<_After_Node>(_frame));
        _stack.emplace_back(_Combine_Node{std::move(_result), std::move(_f.a2),
                                          _f.a1, std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_Node>(_frame));
        _result = f0(std::move(_f.a0), std::move(_result), _f.a1,
                     std::move(_f.a2), std::move(_f._result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rec(T1 f, F1 &&f0,
                     const tree &t) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      const tree *t;
    };

    /// _After_Node: saves [a0_0, a2, a1, a0_1], dispatches next recursive call.
    struct _After_Node {
      const tree *a0_0;
      tree a2;
      uint64_t a1;
      tree a0_1;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      std::decay_t<T1> _result;
      tree a2;
      uint64_t a1;
      tree a0;
    };

    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_rec: _Enter -> _After_Node -> _Combine_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(_After_Node{crane_raw(a0), *a2, a1, *a0});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        }
      } else if (std::holds_alternative<_After_Node>(_frame)) {
        auto _f = std::move(std::get<_After_Node>(_frame));
        _stack.emplace_back(_Combine_Node{std::move(_result), std::move(_f.a2),
                                          _f.a1, std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_Node>(_frame));
        _result = f0(std::move(_f.a0), std::move(_result), _f.a1,
                     std::move(_f.a2), std::move(_f._result));
      }
    }
    return _result;
  }

  static uint64_t tree_sum(const tree &t);
  static uint64_t tree_size(const tree &t);
  static std::pair<tree, uint64_t> sum_with_original(tree t);
  static inline const uint64_t test_sum_with_original = []() {
    std::pair<tree, uint64_t> r = sum_with_original(tree::node(
        tree::node(tree::leaf(), UINT64_C(3), tree::leaf()), UINT64_C(7),
        tree::node(tree::leaf(), UINT64_C(11), tree::leaf())));
    return (r.second + tree_sum(r.first));
  }();
  static std::pair<tree, tree> dup_and_double(tree t);
  static inline const uint64_t test_dup_and_double = []() {
    std::pair<tree, tree> r = dup_and_double(tree::node(
        tree::node(tree::leaf(), UINT64_C(3), tree::leaf()), UINT64_C(5),
        tree::node(tree::leaf(), UINT64_C(7), tree::leaf())));
    return (tree_sum(r.first) + tree_sum(r.second));
  }();
  static std::pair<std::pair<tree, tree>, uint64_t>
  collect_children(const tree &t);
  static inline const uint64_t test_collect_children = []() {
    std::pair<std::pair<tree, tree>, uint64_t> r = collect_children(tree::node(
        tree::node(tree::leaf(), UINT64_C(2), tree::leaf()), UINT64_C(5),
        tree::node(tree::leaf(), UINT64_C(8), tree::leaf())));
    auto [p, s] = std::move(r);
    auto [left_child, right_child] = std::move(p);
    return (
        (tree_sum(std::move(left_child)) + tree_sum(std::move(right_child))) +
        s);
  }();
  static std::pair<tree, uint64_t> sum_with_acc(const tree &t, uint64_t acc);
  static inline const uint64_t test_sum_with_acc = []() {
    std::pair<tree, uint64_t> r = sum_with_acc(
        tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                   UINT64_C(2),
                   tree::node(tree::leaf(), UINT64_C(3), tree::leaf())),
        UINT64_C(0));
    return (r.second + tree_sum(r.first));
  }();
  static std::pair<uint64_t, uint64_t> interleaved_ops(const tree &t);
  static inline const uint64_t test_interleaved_ops = []() {
    std::pair<uint64_t, uint64_t> r = interleaved_ops(tree::node(
        tree::node(tree::leaf(), UINT64_C(2), tree::leaf()), UINT64_C(5),
        tree::node(tree::leaf(), UINT64_C(3), tree::leaf())));
    return (r.first + r.second);
  }();
  static uint64_t flatten_tree_of_trees(const tree &t, tree inner);
  static inline const uint64_t test_flatten_tree_of_trees =
      flatten_tree_of_trees(
          tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                     UINT64_C(2),
                     tree::node(tree::leaf(), UINT64_C(3), tree::leaf())),
          tree::node(tree::leaf(), UINT64_C(10), tree::leaf()));
  static uint64_t mixed_recurse(tree t, uint64_t n);
  static inline const uint64_t test_mixed_recurse = mixed_recurse(
      tree::node(tree::leaf(), UINT64_C(5), tree::leaf()), UINT64_C(1));
  static std::pair<tree, uint64_t> annotate_sizes(const tree &t);
  static inline const uint64_t test_annotate_sizes = []() {
    std::pair<tree, uint64_t> r = annotate_sizes(tree::node(
        tree::node(tree::leaf(), UINT64_C(10), tree::leaf()), UINT64_C(20),
        tree::node(tree::leaf(), UINT64_C(30), tree::leaf())));
    return (tree_sum(r.first) + r.second);
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE23
