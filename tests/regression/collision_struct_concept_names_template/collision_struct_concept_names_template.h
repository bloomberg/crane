#ifndef INCLUDED_COLLISION_STRUCT_CONCEPT_NAMES_TEMPLATE
#define INCLUDED_COLLISION_STRUCT_CONCEPT_NAMES_TEMPLATE

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
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        auto _value = std::move(_loop_m);
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

struct Color {
  // TYPES
  struct Red {
    Nat k;
  };

  struct Mix {
    std::shared_ptr<Color> a;
    std::shared_ptr<Color> b;
  };

  using variant_t = std::variant<Red, Mix>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Color() {}

  explicit Color(Red _v) : v_(std::move(_v)) {}

  explicit Color(Mix _v) : v_(std::move(_v)) {}

  static Color red(Nat k) { return Color(Red{std::move(k)}); }

  static Color mix(Color a, Color b) {
    return Color(Mix{std::make_shared<Color>(std::move(a)),
                     std::make_shared<Color>(std::move(b))});
  }

  // MANIPULATORS
  ~Color() {
    if (std::holds_alternative<Red>(v_mut())) {
      return;
    }
    if (auto *_alt = std::get_if<Mix>(&v_mut())) {
      if (!((_alt->a && _alt->a.use_count() == 1) ||
            (_alt->b && _alt->b.use_count() == 1))) {
        return;
      }
    }
    crane::small_vector<std::shared_ptr<Color>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Mix>(&_v)) {
        if (_alt->a && _alt->a.use_count() == 1) {
          _stack.push_back(std::move(_alt->a));
        }
        if (_alt->b && _alt->b.use_count() == 1) {
          _stack.push_back(std::move(_alt->b));
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

  Color(const Color &) = default;
  Color &operator=(const Color &) = default;
  Color(Color &&) = default;
  Color &operator=(Color &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Shape {
  // TYPES
  struct Circle {
    Nat r;
    Color c;
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

  static Shape circle(Nat r, Color c) {
    return Shape(Circle{std::move(r), std::move(c)});
  }

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
};

template <typename A> struct Box {
  // DATA
  A a;
  Shape s;

  // ACCESSORS
  Box<A> clone() const { return {a, s}; }

  template <typename CraneU> operator Box<CraneU>() const {
    return {[&]() -> CraneU {
              if constexpr (crane_convertible<CraneU, const A &>) {
                return crane_convert<CraneU>(a);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            s};
  }

  // CREATORS
  static Box<A> box0(A a, Shape s) { return {std::move(a), std::move(s)}; }
};

template <typename I, typename A>
concept Shaped = requires {
  { I::shape_of(std::declval<A>()) } -> std::convertible_to<Shape>;
  { I::boxed(std::declval<A>()) } -> std::convertible_to<Box<A>>;
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

struct CollisionStructConceptNamesTemplate {
  static Nat helper(const Nat &n);
  using Color = ::Color;
  using Shape = ::Shape;
  static Nat size(const Shape &x);
  template <typename A> using Box = ::Box<A>;
  static Nat first(const List<Nat> &l);

  struct shaped_nat {
    static Shape shape_of(Nat n) {
      return Shape::square(n, Shape::circle(n, Color::red(n)));
    }

    static Box<Nat> boxed(Nat n) {
      return Box<Nat>::box0(n, Shape::circle(n, Color::red(Nat::o())));
    }
  };

  static_assert(Shaped<shaped_nat, Nat>);
  static inline const Nat sz = CollisionStructConceptNamesTemplate::size(
      CollisionStructConceptNamesTemplate::shaped_nat::shape_of(
          Nat::s(Nat::s(Nat::s(Nat::o())))));
  static inline const Nat bx = []() {
    const auto &_sv = CollisionStructConceptNamesTemplate::shaped_nat::boxed(
        Nat::s(Nat::s(Nat::o())));
    const auto &[a0, s0] = _sv;
    return a0.add(CollisionStructConceptNamesTemplate::size(s0));
  }();
  static Nat head_or_zero(const List<Nat> &x0_);
};

#endif // INCLUDED_COLLISION_STRUCT_CONCEPT_NAMES_TEMPLATE
