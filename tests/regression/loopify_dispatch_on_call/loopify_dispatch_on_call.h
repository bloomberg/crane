#pragma once

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

struct LoopifyDispatchOnCall {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> l;
      std::shared_ptr<tree> r;
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

    static tree node(crane::shared_child_slot<tree> l,
                     crane::shared_child_slot<tree> r) {
      return tree(Node{l.take(), r.take()});
    }

    // MANIPULATORS
    ~tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Node>(&v_mut())) {
        if (!((_alt->l && _alt->l.use_count() == 1) ||
              (_alt->r && _alt->r.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            _stack.push_back(std::move(_alt->l));
          }
          if (_alt->r && _alt->r.use_count() == 1) {
            _stack.push_back(std::move(_alt->r));
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
      std::shared_ptr<tree> l0;
      const tree *r0;
    };

    struct _after_tree_rect_in_Node_2 {
      std::shared_ptr<tree> l0;
      const tree *r0;
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
          const auto &[l0, r0] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(_after_tree_rect_in_Node{l0, crane_raw(r0)});
          _stack.emplace_back(_call{crane_raw(l0)});
        }
      } else if (std::holds_alternative<_after_tree_rect_in_Node>(_popped)) {
        auto _f = std::move(std::get<_after_tree_rect_in_Node>(_popped));
        _stack.pop_back();
        std::shared_ptr<tree> l0 = std::move(_f.l0);
        const tree &r0 = *_f.r0;
        _stack.emplace_back(
            _after_tree_rect_in_Node_2{std::move(l0), &r0, std::move(_result)});
        _stack.emplace_back(_call{&r0});
      } else {
        auto _f = std::move(std::get<_after_tree_rect_in_Node_2>(_popped));
        _stack.pop_back();
        std::shared_ptr<tree> l0 = std::move(_f.l0);
        const tree &r0 = *_f.r0;
        _result = f0(*l0, std::move(_f._tmp2), r0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    return tree_rect<T1>(std::move(f), f0, t);
  }

  static bool parity(const tree &t);
  static tree graft(const tree &t);
  static uint64_t size(const tree &t);
  static tree comb(uint64_t n);
};
