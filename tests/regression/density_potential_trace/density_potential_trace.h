#ifndef INCLUDED_DENSITY_POTENTIAL_TRACE
#define INCLUDED_DENSITY_POTENTIAL_TRACE

#include <crane_real.h>
#include <cstdint>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

struct DensityPotentialTraceCase {
  template <MapsTo<Real, Real> F0, MapsTo<Real, Real> F1>
  __attribute__((pure)) static Real lapse(F0 &&f, F1 &&mu, const Real x) {
    return f(mu(x));
  }

  template <MapsTo<Real, Real> F0, MapsTo<Real, Real> F1>
  __attribute__((pure)) static Real
  proper_time_static(F0 &&f, F1 &&mu, const Real x, const Real t) {
    return (lapse(f, mu, x) * t);
  }

  template <MapsTo<Real, Real> F0, MapsTo<Real, Real> F1, MapsTo<Real, Real> F2,
            MapsTo<Real, Real> F3>
  __attribute__((pure)) static Real
  proper_time_density_path(F0 &&f, F1 &&mu, F2 &&gamma, F3 &&v, const Real t) {
    return r_sqrt((r_pow(lapse(f, mu, gamma(t)), 2u) - r_pow(v(t), 2u)));
  }

  template <MapsTo<Real, Real> F0>
  __attribute__((pure)) static Real V_eff(F0 &&n, const Real x) {
    return r_inv((n(x) * n(x)));
  }

  template <MapsTo<Real, Real> F0>
  __attribute__((pure)) static Real V_eff_massive(F0 &&n, const Real m,
                                                  const Real x) {
    return (r_pow(m, 2u) * V_eff(n, x));
  }

  __attribute__((pure)) static Real sample_activation(const Real z);
  __attribute__((pure)) static Real sample_mu(const Real x);
  __attribute__((pure)) static Real sample_gamma(const Real t);
  __attribute__((pure)) static Real sample_v(const Real _x);
  __attribute__((pure)) static Real sample_N(const Real x);
  static inline const Real sample_mass = Real::from_z(INT64_C(3));
  static inline const Real sample_time = Real::from_z(INT64_C(2));
  __attribute__((pure)) static Real density_radicand_at(const unsigned int &n);
  __attribute__((pure)) static bool
  static_time_nonnegative_at(const unsigned int &n);
  __attribute__((pure)) static bool
  density_radicand_nonnegative_at(const unsigned int &n);
  __attribute__((pure)) static Real density_value_at(const unsigned int &n);
  __attribute__((pure)) static bool
  density_value_nonnegative_at(const unsigned int &n);
  __attribute__((pure)) static bool
  massive_potential_nonnegative_at(const unsigned int &n);
  static inline const bool sample_static_nonneg =
      static_time_nonnegative_at(1u);
  static inline const bool sample_density_radicand_nonneg =
      density_radicand_nonnegative_at(1u);
  static inline const bool sample_density_value_nonneg =
      density_value_nonnegative_at(1u);
  static inline const bool sample_massive_nonneg =
      massive_potential_nonnegative_at(2u);
};

#endif // INCLUDED_DENSITY_POTENTIAL_TRACE
