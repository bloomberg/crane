#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <crane_itree.h>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
struct AE;

struct AppliedTypenameNotHk {
  static std::shared_ptr<ITree<Nat>> use(const Nat &n);
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

struct AE {
  // DATA
  Nat a0_0;

  // ACCESSORS
  AE clone() const { return {a0_0}; }

  // CREATORS
  static AE a0(Nat a0_0) { return {std::move(a0_0)}; }

  template <typename T2> std::shared_ptr<ITree<T2>> handle() const {
    const auto &[a0] = *this;
    return itree_ret(crane_convert<T2>(a0));
  }
};

template <typename T1> std::shared_ptr<ITree<crane::obj>> E_trigger(T1 e) {
  return itree_trigger(std::move(e));
}

template <typename T2> std::shared_ptr<ITree<crane::obj>> F_trigger(T2 e) {
  return itree_trigger(std::move(e));
}

std::shared_ptr<ITree<crane::obj>>
h(Sum1<crane::obj, Sum1<AE, crane::obj, crane::obj>, crane::obj> x);
