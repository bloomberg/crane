#ifndef INCLUDED_ERROR_CTOR_THROUGH_REIFIED_INSTANCE
#define INCLUDED_ERROR_CTOR_THROUGH_REIFIED_INSTANCE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <functional>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct EOU;
struct EOU_monad;
struct Dv;

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

template <typename I>
concept Monad = requires {
  typename I::template m<std::any>;
  {
    I::template ret<std::any>(std::declval<std::any>())
  } -> std::convertible_to<typename I::template m<std::any>>;
  {
    I::template bind<std::any, std::any>(
        std::declval<typename I::template m<std::any>>(),
        std::declval<
            std::function<typename I::template m<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template m<std::any>>;
};

struct PeanoNat {
  static bool eqb(const Nat &n, const Nat &m);
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
};

struct EOU_monad {
  template <typename _A0> using m = EOU<_A0>;

  template <typename _A0> static EOU<_A0> ret(_A0 a) {
    return EOU<_A0>::ok(std::move(a));
  }

  template <typename _A0, typename _A1>
  static EOU<_A1> bind(EOU<_A0> m, std::function<EOU<_A1>(_A0)> k) {
    if (std::holds_alternative<typename EOU<_A0>::Ok>(m.v())) {
      const auto &[a00] = std::get<typename EOU<_A0>::Ok>(m.v());
      return k(a00);
    } else {
      const auto &[a00] = std::get<typename EOU<_A0>::Err>(m.v());
      return EOU<_A1>::err(a00);
    }
  }
};

static_assert(Monad<EOU_monad>);

struct Dv {
  // TYPES
  struct DvBool {
    bool a0;
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

  static Dv dvbool(bool a0) { return Dv(DvBool{a0}); }

  static Dv dvnat(Nat a0) { return Dv(DvNat{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct ErrorCtorThroughReifiedInstance {
  static EOU<Dv> eval_icmp(const Nat &x, const Nat &y);
  static inline const Nat run = []() {
    auto &&_sv = eval_icmp(Nat::s(Nat::o()), Nat::s(Nat::o()));
    if (std::holds_alternative<typename EOU<Dv>::Ok>(_sv.v())) {
      const auto &[a0] = std::get<typename EOU<Dv>::Ok>(_sv.v());
      if (std::holds_alternative<typename Dv::DvBool>(a0.v())) {
        const auto &[a00] = std::get<typename Dv::DvBool>(a0.v());
        if (a00) {
          return Nat::s(Nat::o());
        } else {
          return Nat::o();
        }
      } else {
        return Nat::o();
      }
    } else {
      return Nat::o();
    }
  }();
};

#endif // INCLUDED_ERROR_CTOR_THROUGH_REIFIED_INSTANCE
