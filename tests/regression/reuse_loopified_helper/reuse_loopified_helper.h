#pragma once

#include <cstdint>
#include <utility>
#define CRANE_NON_ATOMIC_RC 1
#include "crane_fn.h"
#include "crane_variant.h"
#include "rc.h"
#include "shared_variant.h"
#include "small_vector.h"

struct Nat {};

struct ReuseLoopifiedHelper {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      crane::shared_box<tree> a0;
      uint64_t a1;
      crane::shared_box<tree> a2;
    };

    using variant_t = crane::shared_variant<Leaf, Node>;

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
      return tree(Node{crane::shared_box<tree>::make(std::move(a0)), a1,
                       crane::shared_box<tree>::make(std::move(a2))});
    }

    static tree node_crane_reuse(tree _tok, tree a0, uint64_t a1, tree a2) {
      auto _alt = Node{crane::shared_box<tree>::make(std::move(a0)), a1,
                       crane::shared_box<tree>::make(std::move(a2))};
      if (_tok.v_.try_reuse(std::move(_alt))) {
        return _tok;
      }
      return tree(Node{std::move(_alt)});
    }

    // MANIPULATORS
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
      crane::shared_box<tree> a0;
      uint64_t a1;
      const tree *a2;
    };

    struct _after_tree_rect_in_Node_2 {
      crane::shared_box<tree> a0;
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
      if (crane::holds_alternative<_call>(_popped)) {
        auto _f = std::move(crane::get<_call>(_popped));
        _stack.pop_back();
        const tree &t = *_f.t;
        if (crane::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2] = crane::get<typename tree::Node>(t.v());
          _stack.emplace_back(_after_tree_rect_in_Node{a0, a1, crane_raw(a2)});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      } else if (crane::holds_alternative<_after_tree_rect_in_Node>(_popped)) {
        auto _f = std::move(crane::get<_after_tree_rect_in_Node>(_popped));
        _stack.pop_back();
        crane::shared_box<tree> a0 = std::move(_f.a0);
        uint64_t a1 = _f.a1;
        const tree &a2 = *_f.a2;
        _stack.emplace_back(_after_tree_rect_in_Node_2{std::move(a0), a1, &a2,
                                                       std::move(_result)});
        _stack.emplace_back(_call{&a2});
      } else {
        auto _f = std::move(crane::get<_after_tree_rect_in_Node_2>(_popped));
        _stack.pop_back();
        crane::shared_box<tree> a0 = std::move(_f.a0);
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

  /// Rebuilds the root's constructor: a candidate for reuse.
  static tree bump_root(tree t);
  static tree insert(uint64_t x, const tree &t);
  static uint64_t sum(const tree &t);
};
