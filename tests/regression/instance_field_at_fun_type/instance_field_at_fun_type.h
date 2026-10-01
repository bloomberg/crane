#ifndef INCLUDED_INSTANCE_FIELD_AT_FUN_TYPE
#define INCLUDED_INSTANCE_FIELD_AT_FUN_TYPE

#include "fn.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <utility>
#include <variant>

struct Nat;

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
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// A class field whose instance is at a function type.  d := S is emitted as
/// static Nat d(Nat x), absorbing the argument, so the value no longer has the
/// field's type and the instance fails its own concept check.

template <typename I, typename A>
concept D = requires {
  { I::d() } -> std::convertible_to<A>;
};

struct InstanceFieldAtFunType {
  struct dn {
    static Nat d() { return Nat::o(); }
  };

  static_assert(D<dn, Nat>);

  struct df {
    static crane::fn<Nat(Nat)> d() {
      return [](const Nat &x) { return Nat::s(x); };
    }
  };

  static_assert(D<df, crane::fn<Nat(Nat)>>);
  static Nat ex(const Nat &x0_);
  static inline const Nat run = ex(Nat::s(Nat::o()));
};

#endif // INCLUDED_INSTANCE_FIELD_AT_FUN_TYPE
