#ifndef INCLUDED_DENSITY_POTENTIAL_TRACE
#define INCLUDED_DENSITY_POTENTIAL_TRACE

#include <crane_real.h>
#include <cstdint>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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
  __attribute__((pure)) static Real density_radicand_at(const unsigned int n);
  __attribute__((pure)) static bool
  static_time_nonnegative_at(const unsigned int n);
  __attribute__((pure)) static bool
  density_radicand_nonnegative_at(const unsigned int n);
  __attribute__((pure)) static Real density_value_at(const unsigned int n);
  __attribute__((pure)) static bool
  density_value_nonnegative_at(const unsigned int n);
  __attribute__((pure)) static bool
  massive_potential_nonnegative_at(const unsigned int n);
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
