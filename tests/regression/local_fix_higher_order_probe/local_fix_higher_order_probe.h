#ifndef INCLUDED_LOCAL_FIX_HIGHER_ORDER_PROBE
#define INCLUDED_LOCAL_FIX_HIGHER_ORDER_PROBE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::unique_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  Nat(const Nat &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Nat(Nat &&_other) : d_v_(std::move(_other.d_v_)) {}

  Nat &operator=(const Nat &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Nat &operator=(Nat &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Nat clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<O>(_sv.v())) {
      return Nat(O{});
    } else {
      const auto &[d_a0] = std::get<S>(_sv.v());
      return Nat(S{d_a0 ? std::make_unique<Nat>(d_a0->clone()) : nullptr});
    }
  }

  // CREATORS
  __attribute__((pure)) static Nat o() { return Nat(O{}); }

  __attribute__((pure)) static Nat s(Nat a0) {
    return Nat(S{std::make_unique<Nat>(std::move(a0))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename T1>
T1 _sample_go(const std::function<T1(Nat)> k, const Nat n0) {
  if (std::holds_alternative<typename Nat::O>(n0.v())) {
    return k(Nat::o());
  } else {
    const auto &[d_a0] = std::get<typename Nat::S>(n0.v());
    Nat d_a0_value = Nat(*(d_a0));
    return _sample_go<T1>([=](Nat x) mutable { return k(Nat::s(x)); },
                          d_a0_value);
  }
}

struct LocalFixHigherOrderProbe {
  __attribute__((pure)) static Nat sample(const Nat &n);
  static inline const Nat run = sample(Nat::s(Nat::s(Nat::s(Nat::o()))));
};

#endif // INCLUDED_LOCAL_FIX_HIGHER_ORDER_PROBE
