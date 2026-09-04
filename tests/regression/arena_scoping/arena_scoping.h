#ifndef INCLUDED_ARENA_SCOPING
#define INCLUDED_ARENA_SCOPING

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#define CRANE_ARENA 1
#include "arena.h"
#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>

struct Nat;

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

  static Nat s(Nat a0) {
    return Nat(S{crane::arena_make_shared<Nat>(std::move(a0))});
  }

  // MANIPULATORS
  ~Nat() {
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
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

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat add(Nat m) const {
    std::shared_ptr<Nat> _head{};
    std::shared_ptr<Nat> *_write = &_head;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        *_write = std::make_shared<Nat>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = std::make_shared<Nat>(typename Nat::S(nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename Nat::S>((*_write)->v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_head);
  }
};

template <typename A> struct Tree {
  // TYPES
  struct Leaf {};

  struct Node {
    std::shared_ptr<Tree<A>> t1;
    A x;
    std::shared_ptr<Tree<A>> t2;
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

  template <typename _U> Tree(const Tree<_U> &_other) {
    if (std::holds_alternative<typename Tree<_U>::Leaf>(_other.v())) {
      this->v_ = Leaf{};
    } else {
      const auto &[t1, x, t2] = std::get<typename Tree<_U>::Node>(_other.v());
      this->v_ = Node{t1 ? std::make_shared<Tree<A>>(*t1) : nullptr,
                      [&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>)
                          return crane_any_cast<A>(x);
                        else
                          return A(x);
                      }(),
                      t2 ? std::make_shared<Tree<A>>(*t2) : nullptr};
    }
  }

  static Tree<A> leaf() { return Tree<A>(Leaf{}); }

  static Tree<A> node(Tree<A> t1, A x, Tree<A> t2) {
    return Tree<A>(Node{crane::arena_make_shared<Tree<A>>(std::move(t1)),
                        std::move(x),
                        crane::arena_make_shared<Tree<A>>(std::move(t2))});
  }

  // MANIPULATORS
  ~Tree() {
    crane::small_vector<std::shared_ptr<Tree<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Node>(&_v)) {
        if (_alt->t1) {
          _stack.push_back(std::move(_alt->t1));
        }
        if (_alt->t2) {
          _stack.push_back(std::move(_alt->t2));
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
  Tree(Tree &&) noexcept = default;
  Tree &operator=(Tree &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, Tree<A> &, T1 &, A &, Tree<A> &,
                                   T1 &>
  T1 tree_rect(T1 f, F1 &&f0) const {
    if (std::holds_alternative<typename Tree<A>::Leaf>(this->v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename Tree<A>::Node>(this->v());
      return f0(*a0, a0->template tree_rect<T1>(f, f0), a1, *a2,
                a2->template tree_rect<T1>(f, f0));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, Tree<A> &, T1 &, A &, Tree<A> &,
                                   T1 &>
  T1 tree_rec(T1 f, F1 &&f0) const {
    if (std::holds_alternative<typename Tree<A>::Leaf>(this->v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename Tree<A>::Node>(this->v());
      return f0(*a0, a0->template tree_rec<T1>(f, f0), a1, *a2,
                a2->template tree_rec<T1>(f, f0));
    }
  }

  Nat size() const {
    if (std::holds_alternative<typename Tree<A>::Leaf>(this->v())) {
      return Nat::s(Nat::o());
    } else {
      const auto &[a0, a1, a2] = std::get<typename Tree<A>::Node>(this->v());
      return Nat::s(Nat::o()).add(a0->size()).add(a2->size());
    }
  }
};

#endif // INCLUDED_ARENA_SCOPING
