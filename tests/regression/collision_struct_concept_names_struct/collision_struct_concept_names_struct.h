#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;

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

  Nat add(Nat m) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const Nat *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        auto _value = std::move(m);
        (_write ? *(*_write = std::make_shared<Nat>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = typename Nat::S(nullptr);
        Nat &_node =
            (_write ? *(*_write = std::make_shared<Nat>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename Nat::S>(_node.v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct Shape {
  // TYPES
  struct Circle {
    Nat r;
  };

  struct Square {
    Nat s;
    std::shared_ptr<Shape> t;
  };

  using variant_t = std::variant<Circle, Square>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Shape() {}

  explicit Shape(Circle _v) : v_(std::move(_v)) {}

  explicit Shape(Square _v) : v_(std::move(_v)) {}

  static Shape circle(Nat r) { return Shape(Circle{std::move(r)}); }

  static Shape square(Nat s, crane::shared_child_slot<Shape> t) {
    return Shape(Square{std::move(s), t.take()});
  }

  // MANIPULATORS
  ~Shape() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Shape> {
      if (auto *_alt = std::get_if<Square>(&_v)) {
        if (_alt->t && _alt->t.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->t);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Shape> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Shape(const Shape &) = default;
  Shape &operator=(const Shape &) = default;
  Shape(Shape &&) = default;
  Shape &operator=(Shape &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat size() const {
    const Shape *_self = this;

    // Explicit stack replaces the non-tail recursion of size: _call frames are
    // pending calls, _after frames resume a caller.
    struct _call {
      const Shape *_self;
    };

    struct _after_size_in_Square {
      Nat s0;
    };

    using _frame = std::variant<_call, _after_size_in_Square>;
    Nat _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const Shape *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename Shape::Circle>(_sv.v())) {
          const auto &[r0] = std::get<typename Shape::Circle>(_sv.v());
          _result = std::move(r0);
        } else {
          const auto &[s0, t0] = std::get<typename Shape::Square>(_sv.v());
          _stack.emplace_back(_after_size_in_Square{s0});
          _stack.emplace_back(_call{crane_raw(t0)});
        }
      } else {
        auto _f = std::move(std::get<_after_size_in_Square>(_popped));
        _stack.pop_back();
        Nat s0 = std::move(_f.s0);
        _result = s0.add(std::move(_result));
      }
    }
    return _result;
  }
};

template <typename I, typename A>
concept Shaped = requires {
  { I::shape_of(std::declval<A>()) } -> std::convertible_to<Shape>;
};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct CollisionStructConceptNamesStruct {
  using Shape = ::Shape;
  static Nat first(const List<Nat> &l);

  struct shaped_nat {
    static Shape shape_of(Nat n) { return Shape::square(n, Shape::circle(n)); }
  };

  static_assert(Shaped<shaped_nat, Nat>);
  static inline const Nat sz =
      CollisionStructConceptNamesStruct::shaped_nat::shape_of(
          Nat::s(Nat::s(Nat::s(Nat::o()))))
          .size();
  static Nat head_or_zero(const List<Nat> &x0_);
};
