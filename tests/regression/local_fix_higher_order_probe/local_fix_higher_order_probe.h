#ifndef INCLUDED_LOCAL_FIX_HIGHER_ORDER_PROBE
#define INCLUDED_LOCAL_FIX_HIGHER_ORDER_PROBE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Nat> o() { return std::make_shared<Nat>(O{}); }

  static std::shared_ptr<Nat> s(const std::shared_ptr<Nat> &a0) {
    return std::make_shared<Nat>(S{a0});
  }

  static std::shared_ptr<Nat> s(std::shared_ptr<Nat> &&a0) {
    return std::make_shared<Nat>(S{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename T1>
T1 _sample_go(const std::function<T1(std::shared_ptr<Nat>)> k,
              const std::shared_ptr<Nat> &n0) {
  if (std::holds_alternative<typename Nat::O>(n0->v())) {
    return k(Nat::o());
  } else {
    const auto &[d_a0] = std::get<typename Nat::S>(n0->v());
    return _sample_go<T1>(
        [=](std::shared_ptr<Nat> x) mutable { return k(Nat::s(x)); }, d_a0);
  }
}

struct LocalFixHigherOrderProbe {
  static std::shared_ptr<Nat> sample(const std::shared_ptr<Nat> &n);
  static inline const std::shared_ptr<Nat> run =
      sample(Nat::s(Nat::s(Nat::s(Nat::o()))));
};

#endif // INCLUDED_LOCAL_FIX_HIGHER_ORDER_PROBE
