#ifndef INCLUDED_TY
#define INCLUDED_TY

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

namespace Ty {

template <typename A> struct Tree;
template <typename A> struct Forest;
template <typename A> struct tree;
template <typename A> struct forest;

template <typename A> struct Tree {
  // TYPES
  struct Node {
    A a0;
    std::shared_ptr<Forest<A>> a1;
  };

  using variant_t = std::variant<Node>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Tree() {}

  explicit Tree(Node _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  Tree(const Tree<CraneU> &_other)
      : v_([&]() -> variant_t {
          const auto &[a0, a1] =
              std::get<typename Tree<CraneU>::Node>(_other.v());
          return Node{
              [&]() -> A {
                if constexpr (crane_convertible<A, const CraneU &>) {
                  return crane_convert<A>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }(),
              (a1 ? std::make_shared<Forest<A>>(crane_convert<Forest<A>>(*a1))
                  : nullptr)};
        }()) {}

  static Tree<A> node(A a0, Forest<A> a1);
  // MANIPULATORS
  ~Tree();
  Tree(const Tree &) = default;
  Tree &operator=(const Tree &) = default;
  Tree(Tree &&) = default;
  Tree &operator=(Tree &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A> struct Forest {
  // TYPES
  struct Nil {};

  struct Cons {
    std::shared_ptr<Tree<A>> a0;
    std::shared_ptr<Forest<A>> a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Forest() {}

  explicit Forest(Nil _v) : v_(_v) {}

  explicit Forest(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  Forest(const Forest<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Forest<CraneU>::Nil>(
                  _other.v())) {
            return Nil{};
          } else {
            const auto &[a0, a1] =
                std::get<typename Forest<CraneU>::Cons>(_other.v());
            return Cons{
                (a0 ? std::make_shared<Tree<A>>(crane_convert<Tree<A>>(*a0))
                    : nullptr),
                (a1 ? std::make_shared<Forest<A>>(crane_convert<Forest<A>>(*a1))
                    : nullptr)};
          }
        }()) {}

  static Forest<A> nil();
  static Forest<A> cons(Tree<A> a0, Forest<A> a1);
  // MANIPULATORS
  ~Forest();
  Forest(const Forest &) = default;
  Forest &operator=(const Forest &) = default;
  Forest(Forest &&) = default;
  Forest &operator=(Forest &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A> Tree<A> Tree<A>::node(A a0, Forest<A> a1) {
  return Tree<A>(
      Node{std::move(a0), std::make_shared<Forest<A>>(std::move(a1))});
}

template <typename A> Tree<A>::~Tree() {
  crane::small_vector<crane::obj> _stack = {};
  auto _drain_self = [&](variant_t &_v) {
    if (auto *_alt = std::get_if<Node>(&_v)) {
      if (_alt->a1 && _alt->a1.use_count() == 1) {
        _stack.push_back(std::move(_alt->a1));
      }
    }
  };
  _drain_self(v_mut());
  while (!_stack.empty()) {
    auto _cur = std::move(_stack.back());
    _stack.pop_back();
    if (auto *_sp = crane::any_cast<std::shared_ptr<Tree<A>>>(&_cur)) {
      if (*_sp && (*_sp).use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain_self((*_sp)->v_mut());
      }
    } else {
      if (auto *_sp = crane::any_cast<std::shared_ptr<Forest<A>>>(&_cur)) {
        if (*_sp && (*_sp).use_count() == 1) {
          auto &_pv = (*_sp)->v_mut();
          if (auto *_alt = std::get_if<typename Forest<A>::Cons>(&_pv)) {
            if (_alt->a0 && _alt->a0.use_count() == 1) {
              _stack.push_back(std::move(_alt->a0));
            }
            if (_alt->a1 && _alt->a1.use_count() == 1) {
              _stack.push_back(std::move(_alt->a1));
            }
          }
        }
      }
    }
  }
}

template <typename A> Forest<A> Forest<A>::nil() { return Forest<A>(Nil{}); }

template <typename A> Forest<A> Forest<A>::cons(Tree<A> a0, Forest<A> a1) {
  return Forest<A>(Cons{std::make_shared<Tree<A>>(std::move(a0)),
                        std::make_shared<Forest<A>>(std::move(a1))});
}

template <typename A> Forest<A>::~Forest() {
  crane::small_vector<crane::obj> _stack = {};
  auto _drain_self = [&](variant_t &_v) {
    if (auto *_alt = std::get_if<Cons>(&_v)) {
      if (_alt->a0 && _alt->a0.use_count() == 1) {
        _stack.push_back(std::move(_alt->a0));
      }
      if (_alt->a1 && _alt->a1.use_count() == 1) {
        _stack.push_back(std::move(_alt->a1));
      }
    }
  };
  _drain_self(v_mut());
  while (!_stack.empty()) {
    auto _cur = std::move(_stack.back());
    _stack.pop_back();
    if (auto *_sp = crane::any_cast<std::shared_ptr<Forest<A>>>(&_cur)) {
      if (*_sp && (*_sp).use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain_self((*_sp)->v_mut());
      }
    } else {
      if (auto *_sp = crane::any_cast<std::shared_ptr<Tree<A>>>(&_cur)) {
        if (*_sp && (*_sp).use_count() == 1) {
          auto &_pv = (*_sp)->v_mut();
          if (auto *_alt = std::get_if<typename Tree<A>::Node>(&_pv)) {
            if (_alt->a1 && _alt->a1.use_count() == 1) {
              _stack.push_back(std::move(_alt->a1));
            }
          }
        }
      }
    }
  }
}

} // namespace Ty

#endif // INCLUDED_TY
