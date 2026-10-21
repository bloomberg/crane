#ifndef INCLUDED_COLLISION_STRUCT_CONCEPT_NAMES_STRUCT
#define INCLUDED_COLLISION_STRUCT_CONCEPT_NAMES_STRUCT

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

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
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

  static Shape square(Nat s, Shape t) {
    return Shape(Square{std::move(s), std::make_shared<Shape>(std::move(t))});
  }

  // MANIPULATORS
  ~Shape() {
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

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const Shape *_self;
    };

    /// CraneCont_Square: saves [s0], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Square {
      Nat s0;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Square>;
    Nat _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified size: CraneEnter -> CraneCont_Square.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const Shape *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename Shape::Circle>(_sv.v())) {
          const auto &[r0] = std::get<typename Shape::Circle>(_sv.v());
          _result = std::move(r0);
        } else {
          const auto &[s0, t0] = std::get<typename Shape::Square>(_sv.v());
          _stack.emplace_back(CraneCont_Square{s0});
          _stack.emplace_back(CraneEnter{crane_raw(t0)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Square>(_frame));
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

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
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

#endif // INCLUDED_COLLISION_STRUCT_CONCEPT_NAMES_STRUCT
