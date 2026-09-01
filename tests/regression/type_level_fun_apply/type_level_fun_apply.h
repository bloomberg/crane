#ifndef INCLUDED_TYPE_LEVEL_FUN_APPLY
#define INCLUDED_TYPE_LEVEL_FUN_APPLY

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
#include <type_traits>
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
};

struct TypeLevelFunApply {
  struct ty {
    // TYPES
    struct TNat {};

    struct TArr {
      std::shared_ptr<ty> a0;
      std::shared_ptr<ty> a1;
    };

    using variant_t = std::variant<TNat, TArr>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ty() {}

    explicit ty(TNat _v) : v_(_v) {}

    explicit ty(TArr _v) : v_(std::move(_v)) {}

    static ty tnat() { return ty(TNat{}); }

    static ty tarr(ty a0, ty a1) {
      return ty(TArr{std::make_shared<ty>(std::move(a0)),
                     std::make_shared<ty>(std::move(a1))});
    }

    // MANIPULATORS
    ~ty() {
      crane::small_vector<std::shared_ptr<ty>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<TArr>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
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

    ty(const ty &) = default;
    ty &operator=(const ty &) = default;
    ty(ty &&) noexcept = default;
    ty &operator=(ty &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, ty &, T1 &, ty &, T1 &>
  static T1 ty_rect(T1 f, F1 &&f0, const ty &t) {
    if (std::holds_alternative<typename ty::TNat>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename ty::TArr>(t.v());
      return f0(*a0, ty_rect<T1>(f, f0, *a0), *a1, ty_rect<T1>(f, f0, *a1));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, ty &, T1 &, ty &, T1 &>
  static T1 ty_rec(T1 f, F1 &&f0, const ty &t) {
    if (std::holds_alternative<typename ty::TNat>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename ty::TArr>(t.v());
      return f0(*a0, ty_rec<T1>(f, f0, *a0), *a1, ty_rec<T1>(f, f0, *a1));
    }
  }

  using sem = std::any;
  static sem app(const ty &_x, const ty &_x0, sem f, sem x);
  static inline const Nat test = std::any_cast<Nat>(app(
      ty::tnat(), ty::tnat(), crane_erase_fn([](const auto &n) { return n; }),
      Nat::s(Nat::s(Nat::s(Nat::o())))));
};

#endif // INCLUDED_TYPE_LEVEL_FUN_APPLY
