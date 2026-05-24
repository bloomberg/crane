#ifndef INCLUDED_LOCAL_FIX_HIGHER_ORDER_PROBE
#define INCLUDED_LOCAL_FIX_HIGHER_ORDER_PROBE

#include <functional>
#include <memory>
#include <utility>
#include <variant>

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
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename T1>
T1 _sample_go(const std::function<T1(Nat)> k, const Nat n0) {
  if (std::holds_alternative<typename Nat::O>(n0.v())) {
    return k(Nat::o());
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n0.v());
    const Nat &a0_value = *a0;
    return _sample_go<T1>([=](Nat x) mutable { return k(Nat::s(x)); },
                          a0_value);
  }
}

struct LocalFixHigherOrderProbe {
  static Nat sample(const Nat &n);
  static inline const Nat run = sample(Nat::s(Nat::s(Nat::s(Nat::o()))));
};

#endif // INCLUDED_LOCAL_FIX_HIGHER_ORDER_PROBE
