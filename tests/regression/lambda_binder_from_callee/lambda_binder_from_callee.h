#ifndef INCLUDED_LAMBDA_BINDER_FROM_CALLEE
#define INCLUDED_LAMBDA_BINDER_FROM_CALLEE

#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
using allocationId = crane::obj;
/// A lambda whose binder type the enclosing declaration never mentions.  The
/// only witness is the callee's parameter type at that argument position, so
/// the carrier guess is the one thing reaching the binder and it fills it with
/// whichever associated type it happens to hold.
template <typename I>
concept Prov = requires {
  typename I::provenance;
  typename I::allocationId;
  typename I::prov;
  {
    I::mk_aid(std::declval<Nat>())
  } -> std::convertible_to<typename I::allocationId>;
  {
    I::aid_size(std::declval<typename I::allocationId>())
  } -> std::convertible_to<Nat>;
};
template <typename I>
concept Params = requires {
  typename I::PROV;
  { I::width() } -> std::convertible_to<Nat>;
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

struct LambdaBinderFromCallee {
  template <Params _tcI0, typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, typename _tcI0::PROV::allocationId>
  static T1 with_aid(F0 &&f) {
    return f(_tcI0::PROV::mk_aid(Nat::o()));
  }

  /// use's type is nat; allocationId occurs nowhere in it.
  template <Params _tcI0> static Nat use() {
    return with_aid<_tcI0, Nat>(
        [=](const typename _tcI0::PROV::allocationId &a) {
          return _tcI0::PROV::aid_size(a);
        });
  }
};

#endif // INCLUDED_LAMBDA_BINDER_FROM_CALLEE
