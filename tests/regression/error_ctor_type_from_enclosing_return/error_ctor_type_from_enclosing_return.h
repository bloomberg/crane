#ifndef INCLUDED_ERROR_CTOR_TYPE_FROM_ENCLOSING_RETURN
#define INCLUDED_ERROR_CTOR_TYPE_FROM_ENCLOSING_RETURN

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

enum class Bool0;
struct Nat;
template <typename A> struct EOU;
struct Dv;
enum class Bool0 { TRUE_, FALSE_ };

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

struct PeanoNat {
  static Bool0 eqb(const Nat &n, const Nat &m);
};

template <typename A> struct EOU {
  // TYPES
  struct Ok {
    A a0;
  };

  struct Err {
    Nat a0;
  };

  using variant_t = std::variant<Ok, Err>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  EOU() {}

  explicit EOU(Ok _v) : v_(std::move(_v)) {}

  explicit EOU(Err _v) : v_(std::move(_v)) {}

  template <typename _U> EOU(const EOU<_U> &_other) {
    if (std::holds_alternative<typename EOU<_U>::Ok>(_other.v())) {
      const auto &[a0] = std::get<typename EOU<_U>::Ok>(_other.v());
      this->v_ = Ok{[&]() -> A {
        if constexpr (crane_convertible<A, const _U &>) {
          return crane_convert<A>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    } else {
      const auto &[a0] = std::get<typename EOU<_U>::Err>(_other.v());
      this->v_ = Err{a0};
    }
  }

  static EOU<A> ok(A a0) { return EOU<A>(Ok{std::move(a0)}); }

  static EOU<A> err(Nat a0) { return EOU<A>(Err{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<EOU<T1>, F0 &, A &>
  EOU<T1> bind0(F0 &&k) const {
    if (std::holds_alternative<typename EOU<A>::Ok>(this->v())) {
      const auto &[a0] = std::get<typename EOU<A>::Ok>(this->v());
      return k(a0);
    } else {
      const auto &[a0] = std::get<typename EOU<A>::Err>(this->v());
      return EOU<T1>::err(a0);
    }
  }
};

template <typename T1> EOU<T1> ret(T1 a) { return EOU<T1>::ok(std::move(a)); }

struct Dv {
  // TYPES
  struct DvBool {
    Bool0 a0;
  };

  struct DvNat {
    Nat a0;
  };

  using variant_t = std::variant<DvBool, DvNat>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Dv() {}

  explicit Dv(DvBool _v) : v_(std::move(_v)) {}

  explicit Dv(DvNat _v) : v_(std::move(_v)) {}

  static Dv dvbool(Bool0 a0) { return Dv(DvBool{a0}); }

  static Dv dvnat(Nat a0) { return Dv(DvNat{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct ErrorCtorTypeFromEnclosingReturn {
  static EOU<Dv> eval_icmp(const Nat &x, const Nat &y);
  static inline const Nat run = []() {
    auto &&_sv = eval_icmp(Nat::s(Nat::o()), Nat::s(Nat::o()));
    if (std::holds_alternative<typename EOU<Dv>::Ok>(_sv.v())) {
      const auto &[a0] = std::get<typename EOU<Dv>::Ok>(_sv.v());
      if (std::holds_alternative<typename Dv::DvBool>(a0.v())) {
        const auto &[a00] = std::get<typename Dv::DvBool>(a0.v());
        switch (a00) {
        case Bool0::TRUE_: {
          return Nat::s(Nat::o());
        }
        case Bool0::FALSE_: {
          return Nat::o();
        }
        default:
          std::unreachable();
        }
      } else {
        return Nat::o();
      }
    } else {
      return Nat::o();
    }
  }();
};

#endif // INCLUDED_ERROR_CTOR_TYPE_FROM_ENCLOSING_RETURN
