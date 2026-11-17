#pragma once

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

struct MemSafetyProbe8 {
  /// These tests probe the interaction between:
  /// 1. OWNED tree parameters in loopified functions
  /// 2. Double recursion (f l + v + f r) creating _After frames
  /// 3. The flatten optimization (optimize_frame_push_args) that adds
  /// std::move to _Enter frame pushes
  ///
  /// If an _After frame stores a raw pointer (d_a0.get()) to a child
  /// of an owned tree, and the tree is destroyed at the end of the
  /// _Enter handler, the raw pointer would dangle.
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

    static tree node(crane::shared_child_slot<tree> a0, uint64_t a1,
                     crane::shared_child_slot<tree> a2) {
      return tree(Node{a0.take(), a1, a2.take()});
    }

    // MANIPULATORS
    ~tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Node>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
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
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t) {
    // Explicit stack replaces the non-tail recursion of tree_rect: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const tree *t;
    };

    struct _after_tree_rect_in_Node {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      const tree *a2;
    };

    struct _after_tree_rect_in_Node_2 {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      const tree *a2;
      T1 _tmp2;
    };

    using _frame = std::variant<_call, _after_tree_rect_in_Node,
                                _after_tree_rect_in_Node_2>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&t});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(_after_tree_rect_in_Node{a0, a1, crane_raw(a2)});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_after_tree_rect_in_Node>(_popped)) {
        auto _f = std::move(std::get<_after_tree_rect_in_Node>(_popped));
        _stack.pop_back();
        std::shared_ptr<tree> a0 = std::move(_f.a0);
        uint64_t a1 = _f.a1;
        const tree &a2 = *_f.a2;
        _stack.emplace_back(_after_tree_rect_in_Node_2{std::move(a0), a1, &a2,
                                                       std::move(_result)});
        _stack.emplace_back(_call{&a2});
      } else {
        auto _f = std::move(std::get<_after_tree_rect_in_Node_2>(_popped));
        _stack.pop_back();
        std::shared_ptr<tree> a0 = std::move(_f.a0);
        uint64_t a1 = _f.a1;
        const tree &a2 = *_f.a2;
        _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    return tree_rect<T1>(std::move(f), f0, t);
  }

  /// TEST 1: Non-method tree traversal with double recursion.
  /// dummy ensures tree is NOT the first arg (avoiding methodification).
  /// tree is the second arg — should be owned if it doesn't escape.
  static uint64_t tree_sum_ext(uint64_t _x, const tree &t);
  static inline const uint64_t test_tree_sum = tree_sum_ext(
      UINT64_C(0),
      tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                 UINT64_C(20),
                 tree::node(tree::leaf(), UINT64_C(30), tree::leaf())));
  /// TEST 2: Same but with a more complex computation to prevent
  /// the optimizer from simplifying.
  static uint64_t tree_weighted(uint64_t _x, const tree &t, uint64_t depth);
  static inline const uint64_t test_tree_weighted = tree_weighted(
      UINT64_C(0),
      tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                 UINT64_C(20),
                 tree::node(tree::leaf(), UINT64_C(30), tree::leaf())),
      UINT64_C(1));
  /// TEST 3: Deep tree traversal — more iterations, more frames.
  static tree make_left_spine(uint64_t n);
  static inline const uint64_t test_deep_tree =
      tree_sum_ext(UINT64_C(0), make_left_spine(UINT64_C(100)));
  /// TEST 4: Tree traversal where both recursive calls use
  /// different subtrees — _After frame must hold one while
  /// processing the other.
  static uint64_t tree_collect(uint64_t _x, const tree &t);
  static inline const uint64_t test_collect = tree_collect(
      UINT64_C(0),
      tree::node(
          tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                     UINT64_C(10), tree::leaf()),
          UINT64_C(20),
          tree::node(tree::leaf(), UINT64_C(30),
                     tree::node(tree::leaf(), UINT64_C(40), tree::leaf()))));
  /// TEST 5: Tree function where the tree is consumed (not
  /// used after recursive calls) — maximally owned.
  static uint64_t tree_flatten(uint64_t _x, const tree &t);
  static inline const uint64_t test_flatten = tree_flatten(
      UINT64_C(0),
      tree::node(tree::node(tree::leaf(), UINT64_C(2), tree::leaf()),
                 UINT64_C(3),
                 tree::node(tree::leaf(), UINT64_C(5), tree::leaf())));
  /// TEST 6: Pass tree as a higher-order function argument
  /// to prevent methodification completely.
  static uint64_t tree_size_via_fold(const tree &t);
  static inline const uint64_t test_fold_size = tree_size_via_fold(tree::node(
      tree::node(tree::leaf(), UINT64_C(1), tree::leaf()), UINT64_C(2),
      tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                 UINT64_C(4), tree::leaf())));
};
