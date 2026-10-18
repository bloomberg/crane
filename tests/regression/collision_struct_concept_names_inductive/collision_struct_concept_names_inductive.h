#ifndef INCLUDED_COLLISION_STRUCT_CONCEPT_NAMES_INDUCTIVE
#define INCLUDED_COLLISION_STRUCT_CONCEPT_NAMES_INDUCTIVE

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
using key = Nat;
enum class Color { RED, BLUE };
template <typename I, typename A>
concept Keyed = requires {
  { I::key_of(std::declval<A>()) } -> std::convertible_to<key>;
  { I::color_of(std::declval<A>()) } -> std::convertible_to<Color>;
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

struct PeanoNat {
  static bool eqb(const Nat &n, const Nat &m);
};

struct CollisionStructConceptNamesInductive {
  using key = ::key;
  using Color = ::Color;

  struct keyed_nat {
    static key key_of(Nat n) { return n; }

    static Color color_of(Nat) { return Color::BLUE; }
  };

  static_assert(Keyed<keyed_nat, Nat>);

  template <typename _tcI0, typename T1>
    requires Keyed<_tcI0, T1>
  static bool same(const T1 &x, const T1 &y) {
    return PeanoNat::eqb(
        _tcI0::key_of(x),
        CollisionStructConceptNamesInductive::first(
            List<Nat>::cons(_tcI0::key_of(y), List<Nat>::nil())));
  }

  static inline const bool check =
      CollisionStructConceptNamesInductive::template same<keyed_nat, Nat>(
          Nat::s(Nat::s(Nat::s(Nat::o()))), Nat::s(Nat::s(Nat::s(Nat::o()))));
  static inline const bool blue = []() {
    switch (CollisionStructConceptNamesInductive::keyed_nat::color_of(
        Nat::s(Nat::s(Nat::s(Nat::o()))))) {
    case Color::RED: {
      return false;
    }
    case Color::BLUE: {
      return true;
    }
    default:
      std::unreachable();
    }
  }();
  static Nat first(const List<Nat> &l);
};

#endif // INCLUDED_COLLISION_STRUCT_CONCEPT_NAMES_INDUCTIVE
