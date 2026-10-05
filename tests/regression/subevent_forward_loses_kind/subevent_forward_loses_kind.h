#ifndef INCLUDED_SUBEVENT_FORWARD_LOSES_KIND
#define INCLUDED_SUBEVENT_FORWARD_LOSES_KIND

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

enum class Unit;
struct Nat;
template <typename A> struct List;
template <typename A> struct UBE;
enum class Unit { TT };

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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

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

  Nat length() const {
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = Nat::o();
        (_write ? *(*_write = std::make_shared<Nat>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename Nat::S(nullptr);
        Nat &_node =
            (_write ? *(*_write = std::make_shared<Nat>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename Nat::S>(_node.v_mut()).a0;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

template <typename A> struct UBE {
  // DATA
  Unit a0;

  // ACCESSORS
  UBE<A> clone() const { return {a0}; }

  template <typename CraneU> operator UBE<CraneU>() const { return {a0}; }

  // CREATORS
  static UBE<A> throwub(Unit a0) { return {a0}; }
};

template <typename f, typename g> using Sub = crane::fn<g(f)>;

template <typename T1, typename T2, typename T3>
crane::rebind_t<T2, T3> inj(std::type_identity_t<Sub<T1, T2>> sub,
                            crane::rebind_t<T1, T3> x) {
  return crane_container_cast<crane::rebind_t<T2, T3>>(
      sub(crane_convert<T1>(std::move(x))));
}

template <typename T1 = void, typename T2, typename CraneP0>
List<T2> trigger_cast(CraneP0) {
  return List<T2>::nil();
}

struct SubeventForwardLosesKind {
  template <typename T1, typename T2>
  static List<T2> raiseUB(std::type_identity_t<Sub<UBE<crane::obj>, T1>> s) {
    return trigger_cast<void, T2>(inj<UBE<crane::obj>, T1, Nat>(
        std::move(s), UBE<crane::obj>::throwub(Unit::TT)));
  }

  static UBE<crane::obj> sub_refl(UBE<crane::obj> e);
  static inline const Nat run =
      raiseUB<UBE<crane::obj>, Nat>(sub_refl).length();
};

#endif // INCLUDED_SUBEVENT_FORWARD_LOSES_KIND
