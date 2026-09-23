#ifndef INCLUDED_VALUE_POSITION_CLASS_PROMOTED
#define INCLUDED_VALUE_POSITION_CLASS_PROMOTED

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
template <typename I> struct VLike;

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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ =
          Cons{[&]() -> A {
                 if constexpr (crane_convertible<A, const _U &>) {
                   return crane_convert<A>(a);
                 } else {
                   throw std::logic_error("unreachable: inactive constructor "
                                          "field at this instantiation");
                 }
               }(),
               (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                  : nullptr)};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
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

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

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
  std::function<I(I, I)> vadd;

  // ACCESSORS
  template <typename _U> operator VLike<_U>() const {
    return {[&]() -> _U {
              if constexpr (crane_convertible<_U, const I &>) {
                return crane_convert<_U>(vzero);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            std::function<_U(_U, _U)>(vadd)};
  }
};

/// These two put VLike in value position, which demotes it to a struct.
template <typename T1, typename F1>
  requires std::is_invocable_r_v<T1, F1 &, T1 &, T1 &>
VLike<T1> mk_vlike(T1 z, F1 &&f) {
  return VLike<T1>{std::move(z), f};
}

const List<VLike<Nat>> dicts = List<VLike<Nat>>::cons(
    mk_vlike<Nat>(Nat::o(),
                  [](const Nat &_x0, const Nat &_x1) { return _x0.add(_x1); }),
    List<VLike<Nat>>::nil());
template <typename I>concept Ptr = requires {
  typename I::iptr;
  { I::VLike_iptr() } -> std::convertible_to<VLike<typename I::iptr>>;
} && (requires {
  { I::one_iptr() } -> std::convertible_to<typename I::iptr>;
} || requires {
  { I::one_iptr } -> std::convertible_to<typename I::iptr>;
});
using iptr = std::any;

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
