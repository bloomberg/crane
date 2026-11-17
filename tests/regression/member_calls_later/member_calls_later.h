#pragma once

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
struct Tree;

struct Helper {
  static Nat pick(Nat a, Nat b);
};

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(crane::shared_child_slot<Nat> a0) { return Nat(S{a0.take()}); }

  // MANIPULATORS
  ~Nat() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct PeanoNat {
  static bool leb(const Nat &n, const Nat &m);
};

struct Tree {
  // TYPES
  struct Leaf {};

  struct Node {
    std::shared_ptr<Tree> a0;
    std::shared_ptr<Tree> a1;
  };

  using variant_t = std::variant<Leaf, Node>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Tree() {}

  explicit Tree(Leaf _v) : v_(_v) {}

  explicit Tree(Node _v) : v_(std::move(_v)) {}

  static Tree leaf() { return Tree(Leaf{}); }

  static Tree node(crane::shared_child_slot<Tree> a0,
                   crane::shared_child_slot<Tree> a1) {
    return Tree(Node{a0.take(), a1.take()});
  }

  // MANIPULATORS
  ~Tree() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    if (std::holds_alternative<Leaf>(v_mut())) {
      return;
    }
    if (auto *_alt = std::get_if<Node>(&v_mut())) {
      if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
            (_alt->a1 && _alt->a1.use_count() == 1))) {
        return;
      }
    }
    crane::small_vector<std::shared_ptr<Tree>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Node>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          _stack.push_back(std::move(_alt->a0));
        }
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          _stack.push_back(std::move(_alt->a1));
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

  Tree(const Tree &) = default;
  Tree &operator=(const Tree &) = default;
  Tree(Tree &&) = default;
  Tree &operator=(Tree &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat deeper() const;
};

inline Nat Tree::deeper() const {
  const Tree *_self = this;

  // Explicit stack replaces the non-tail recursion of deeper: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const Tree *_self;
  };

  struct _after_deeper_in_Node {
    const Tree *a1;
  };

  struct _after_deeper_in_Node_2 {
    Nat _tmp2;
  };

  using _frame =
      std::variant<_call, _after_deeper_in_Node, _after_deeper_in_Node_2>;
  Nat _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{_self});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const Tree *_self = _f._self;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename Tree::Leaf>(_sv.v())) {
        _result = Nat::o();
      } else {
        const auto &[a0, a1] = std::get<typename Tree::Node>(_sv.v());
        _stack.emplace_back(_after_deeper_in_Node{crane_raw(a1)});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else if (std::holds_alternative<_after_deeper_in_Node>(_popped)) {
      auto _f = std::move(std::get<_after_deeper_in_Node>(_popped));
      _stack.pop_back();
      const Tree &a1 = *_f.a1;
      _stack.emplace_back(_after_deeper_in_Node_2{std::move(_result)});
      _stack.emplace_back(_call{_f.a1});
    } else {
      auto _f = std::move(std::get<_after_deeper_in_Node_2>(_popped));
      _stack.pop_back();
      _result = Nat::s(Helper::pick(std::move(_f._tmp2), std::move(_result)));
    }
  }
  return _result;
}
