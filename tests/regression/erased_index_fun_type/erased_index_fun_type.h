#ifndef INCLUDED_ERASED_INDEX_FUN_TYPE
#define INCLUDED_ERASED_INDEX_FUN_TYPE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <functional>
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
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// A type-indexed inductive whose index can be a function type.  dflt is
/// declared as returning std::any, and the call site then applies the result
/// directly: "type 'std::any' does not provide a call operator".
struct ErasedIndexFunType {
  struct ty {
    // TYPES
    struct TN {};

    struct TF {
      std::shared_ptr<ty> a;
      std::shared_ptr<ty> b;
    };

    using variant_t = std::variant<TN, TF>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ty() {}

    explicit ty(TN _v) : v_(_v) {}

    explicit ty(TF _v) : v_(std::move(_v)) {}

    static ty tn() { return ty(TN{}); }

    static ty tf(ty a, ty b) {
      return ty(TF{std::make_shared<ty>(std::move(a)),
                   std::make_shared<ty>(std::move(b))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2 = void, typename F1>
  static T1 ty_rect(T1 f, F1 &&f0, const ty &t) {
    if (std::holds_alternative<typename ty::TN>(t.v())) {
      return f;
    } else {
      const auto &[a, b] = std::get<typename ty::TF>(t.v());
      return crane_any_cast<T1>(
          f0(*a, ty_rect(f, f0, *a), *b, ty_rect(f, f0, *b)));
    }
  }

  template <typename T1, typename T2 = void, typename F1>
  static T1 ty_rec(T1 f, F1 &&f0, const ty &t) {
    if (std::holds_alternative<typename ty::TN>(t.v())) {
      return f;
    } else {
      const auto &[a, b] = std::get<typename ty::TF>(t.v());
      return crane_any_cast<T1>(
          f0(*a, ty_rec(f, f0, *a), *b, ty_rec(f, f0, *b)));
    }
  }

  template <typename T1 = void> static crane::obj dflt(const ty &t) {
    if (std::holds_alternative<typename ty::TN>(t.v())) {
      return Nat::o();
    } else {
      const auto &[a, b0] = std::get<typename ty::TF>(t.v());
      return crane_erase_fn(
          [=](const auto &) { return dflt<crane::obj>(*b0); });
    }
  }

  static Nat ex(const Nat &x0_);
  static inline const Nat run =
      ex(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))));
};

#endif // INCLUDED_ERASED_INDEX_FUN_TYPE
