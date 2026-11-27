#pragma once

#include "crane_fn.h"
#include "fn.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// The argument of a beta-redex (fun w : bool -> nat => ...) (let cf := fun _ :
/// tree => 1 in
/// fun c : bool => cf Leaf) binds w and then cf; the C++ lambda for cf
/// takes its parameter type from w's domain (bool) instead of its own
/// binder (tree), so crane::fn<uint64_t(tree)> cf = [](bool) {...} does
/// not compile.  With a domain that converts implicitly (e.g. nat into
/// std::optional) the wrong type compiles silently.
struct LetLambdaSlotBinder {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> a0;
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

    static tree node(crane::shared_child_slot<tree> a0) {
      return tree(Node{a0.take()});
    }

    // MANIPULATORS
    ~tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> std::shared_ptr<tree> {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a0);
          }
        }
        return nullptr;
      };
      std::shared_ptr<tree> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
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
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename tree::Node>(t0.v());
      return f0(*a0, tree_rect<T1>(std::move(f), f0, *a0));
    }
  }

  template <typename T1, typename F1>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t0) {
    return tree_rect<T1>(std::move(f), f0, t0);
  }

  static inline const uint64_t t = []() {
    return []() {
      crane::fn<uint64_t(bool)> w;
      crane::fn<uint64_t(tree)> cf = [](tree) { return UINT64_C(1); };
      w = [=, cf = std::move(cf)](bool) { return cf(tree::leaf()); };
      return w(true) + w(false);
    }();
  }();
};
