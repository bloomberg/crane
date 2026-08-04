#ifndef INCLUDED_ARENA_TREE
#define INCLUDED_ARENA_TREE

#include "arena.h"
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

enum class Bool0 { TRUE_, FALSE_ };

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

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::shared_ptr<Nat>> _stack = {};
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
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat add(Nat m) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return m;
    } else {
      const auto &[a0] = std::get<typename Nat::S>(this->v());
      return Nat::s(a0->add(std::move(m)));
    }
  }
};

template <typename A> struct Tree {
  // TYPES
  struct Leaf {};

  struct Node {
    Tree<A> *t1;
    A x;
    Tree<A> *t2;
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

  static Tree<A> leaf() { return Tree(Leaf{}); }

  static Tree<A> node(Tree<A> t1, A x, Tree<A> t2) {
    return Tree(Node{crane::arena_alloc<Tree<A>>(std::move(t1)), std::move(x),
                     crane::arena_alloc<Tree<A>>(std::move(t2))});
  }

  // MANIPULATORS
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

  Bool0 is_leaf() const {
    if (std::holds_alternative<typename Tree<A>::Leaf>(this->v())) {
      return Bool0::TRUE_;
    } else {
      return Bool0::FALSE_;
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

  Tree<A> mirror() const {
    if (std::holds_alternative<typename Tree<A>::Leaf>(this->v())) {
      return Tree<A>::leaf();
    } else {
      const auto &[a0, a1, a2] = std::get<typename Tree<A>::Node>(this->v());
      return Tree<A>::node(a2->mirror(), a1, a0->mirror());
    }
  }
};

#endif // INCLUDED_ARENA_TREE
