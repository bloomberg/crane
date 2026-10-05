#ifndef INCLUDED_UNDEDUCIBLE_TT_RETURN
#define INCLUDED_UNDEDUCIBLE_TT_RETURN

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename E, typename F, typename X> struct Sum1;
template <typename X> struct ReqA;
template <typename X> struct ReqB;

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

template <typename E, typename F, typename X> struct Sum1 {
  // TYPES
  struct Inl1 {
    crane::rebind_t<E, X> e;
  };

  struct Inr1 {
    crane::rebind_t<F, X> f;
  };

  using variant_t = std::variant<Inl1, Inr1>;
  using crane_family_tag = void;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum1() {}

  explicit Sum1(Inl1 _v) : v_(std::move(_v)) {}

  explicit Sum1(Inr1 _v) : v_(std::move(_v)) {}

  template <typename CraneU0, typename CraneU1, typename CraneU2>
  Sum1(const Sum1<CraneU0, CraneU1, CraneU2> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<
                  typename Sum1<CraneU0, CraneU1, CraneU2>::Inl1>(_other.v())) {
            const auto &[e] =
                std::get<typename Sum1<CraneU0, CraneU1, CraneU2>::Inl1>(
                    _other.v());
            return Inl1{[&]() -> E {
              if constexpr (crane_convertible<E, const CraneU0 &>) {
                return crane_convert<E>(e);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[f] =
                std::get<typename Sum1<CraneU0, CraneU1, CraneU2>::Inr1>(
                    _other.v());
            return Inr1{[&]() -> F {
              if constexpr (crane_convertible<F, const CraneU1 &>) {
                return crane_convert<F>(f);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Sum1<E, F, X> inl1(crane::rebind_t<E, X> e) {
    return Sum1<E, F, X>(Inl1{std::move(e)});
  }

  static Sum1<E, F, X> inr1(crane::rebind_t<F, X> f) {
    return Sum1<E, F, X>(Inr1{std::move(f)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Handler {
  template <typename T1, typename T2, typename T4, typename F0, typename F1>
  static std::invoke_result_t<F0 &, crane::rebind_t<T1, T4> &>
  case_(F0 &&f, F1 &&g, const Sum1<T1, T2, T4> &ab);
};

template <typename X> struct ReqA {
  // DATA
  X x;

  // ACCESSORS
  ReqA<X> clone() const { return {x}; }

  template <typename CraneU> operator ReqA<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const X &>) {
        return crane_convert<CraneU>(x);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }

  // CREATORS
  static ReqA<X> mka(X x) { return {std::move(x)}; }
};

template <typename X> struct ReqB {
  // DATA
  X x;

  // ACCESSORS
  ReqB<X> clone() const { return {x}; }

  template <typename CraneU> operator ReqB<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const X &>) {
        return crane_convert<CraneU>(x);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }

  // CREATORS
  static ReqB<X> mkb(X x) { return {std::move(x)}; }
};

struct UndeducibleTtReturn {
  static std::optional<Nat>
  use(const Sum1<ReqA<crane::obj>, ReqB<crane::obj>, Nat> &ab);
};

template <typename T1, typename T2, typename T4, typename F0, typename F1>
std::invoke_result_t<F0 &, crane::rebind_t<T1, T4> &>
Handler::case_(F0 &&f, F1 &&g, const Sum1<T1, T2, T4> &ab) {
  if (std::holds_alternative<typename Sum1<T1, T2, T4>::Inl1>(ab.v())) {
    const auto &[e0] = std::get<typename Sum1<T1, T2, T4>::Inl1>(ab.v());
    return f(e0);
  } else {
    const auto &[f0] = std::get<typename Sum1<T1, T2, T4>::Inr1>(ab.v());
    return g(f0);
  }
}

#endif // INCLUDED_UNDEDUCIBLE_TT_RETURN
