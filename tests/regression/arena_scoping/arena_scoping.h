#ifndef INCLUDED_ARENA_SCOPING
#define INCLUDED_ARENA_SCOPING

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#define CRANE_ARENA 1
#include "arena.h"
#include "small_vector.h"
#include <atomic>

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
      this->v_ = Node{
          t1 ? std::make_shared<Tree<A>>(*t1) : nullptr,
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (x.type() == typeid(A))
                return std::any_cast<A>(x);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(x);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(x);
            } else
              return A(x);
          }(),
          t2 ? std::make_shared<Tree<A>>(*t2) : nullptr};
    }
  }

  static Tree<A> leaf() { return Tree(Leaf{}); }

  static Tree<A> node(Tree<A> t1, A x, Tree<A> t2) {
    return Tree(Node{crane::arena_make_shared<Tree<A>>(std::move(t1)),
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
