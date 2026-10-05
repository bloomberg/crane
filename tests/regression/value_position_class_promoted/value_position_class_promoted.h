#ifndef INCLUDED_VALUE_POSITION_CLASS_PROMOTED
#define INCLUDED_VALUE_POSITION_CLASS_PROMOTED

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
template <typename I> struct VLike;
using iptr = crane::obj;
template <typename
I>concept Ptr = requires {
    typename I::iptr;
    { I::VLike_iptr() } -> std::convertible_to<VLike<typename I::iptr>>;
  } && (requires {
    { I::one_iptr() } -> std::convertible_to<typename I::iptr>;
  } || requires {
    { I::one_iptr } -> std::convertible_to<typename I::iptr>;
  });

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

/// A class that is also used in value position comes out as a struct, not a
/// concept.  A field of that type is then an ordinary value field, so
/// promoting it to an associated type leaves the concept asking for one name
/// both as a type and as a function -- which no instance can satisfy.
template <typename I> struct VLike {
  I vzero;
  crane::fn<I(I, I)> vadd;

  // ACCESSORS
  template <typename CraneU> operator VLike<CraneU>() const {
    return {[&]() -> CraneU {
              if constexpr (crane_convertible<CraneU, const I &>) {
                return crane_convert<CraneU>(vzero);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            crane_convert<crane::fn<CraneU(CraneU, CraneU)>>(vadd)};
  }
};

/// These two put VLike in value position, which demotes it to a struct.
template <typename T1, typename F1> VLike<T1> mk_vlike(const T1 &z, F1 &&f) {
  return VLike<T1>{z, f};
}

const List<VLike<Nat>> dicts = List<VLike<Nat>>::cons(
    mk_vlike<Nat>(Nat::o(),
                  [](const Nat &_x0, const Nat &_x1) { return _x0.add(_x1); }),
    List<VLike<Nat>>::nil());

struct ValuePositionClassPromoted {
  template <Ptr _tcI0> static typename _tcI0::iptr twice() {
    return _tcI0::VLike_iptr().vadd(_tcI0::one_iptr(), _tcI0::one_iptr());
  }

  /// Reaches dicts, so the value-position use is not pruned.
  static inline const Nat ndicts = []() {
    auto &&_sv = dicts;
    if (std::holds_alternative<typename List<VLike<Nat>>::Nil>(_sv.v())) {
      return Nat::o();
    } else {
      const auto &[a0, a1] = std::get<typename List<VLike<Nat>>::Cons>(_sv.v());
      return a0.vzero;
    }
  }();
};

#endif // INCLUDED_VALUE_POSITION_CLASS_PROMOTED
