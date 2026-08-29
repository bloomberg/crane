#ifndef INCLUDED_DENSITY_POTENTIAL_TRACE
#define INCLUDED_DENSITY_POTENTIAL_TRACE

#include <crane_real.h>
#include <cstdint>
#include <type_traits>

struct DensityPotentialTraceCase {
  template <typename F0, typename F1>
    requires std::is_invocable_r_v<Real, F0 &, Real &> &&
             std::is_invocable_r_v<Real, F1 &, Real &>
  static Real lapse(F0 &&f, F1 &&mu, Real x) {
    return f(mu(x));
  }

  template <typename F0, typename F1>
    requires std::is_invocable_r_v<Real, F0 &, Real &> &&
             std::is_invocable_r_v<Real, F1 &, Real &>
  static Real proper_time_static(F0 &&f, F1 &&mu, Real x, Real t) {
    return (lapse(f, mu, x) * t);
  }

  template <typename F0, typename F1, typename F2, typename F3>
    requires std::is_invocable_r_v<Real, F0 &, Real &> &&
             std::is_invocable_r_v<Real, F1 &, Real &> &&
             std::is_invocable_r_v<Real, F2 &, Real &> &&
             std::is_invocable_r_v<Real, F3 &, Real &>
  static Real proper_time_density_path(F0 &&f, F1 &&mu, F2 &&gamma, F3 &&v,
                                       Real t) {
    return r_sqrt((r_pow(lapse(f, mu, gamma(t)), UINT64_C(2)) -
                   r_pow(v(t), UINT64_C(2))));
  }

  template <typename F0>
    requires std::is_invocable_r_v<Real, F0 &, Real &>
  static Real V_eff(F0 &&n, Real x) {
    return r_inv((n(x) * n(x)));
  }

  template <typename F0>
    requires std::is_invocable_r_v<Real, F0 &, Real &>
  static Real V_eff_massive(F0 &&n, Real m, Real x) {
    return (r_pow(m, UINT64_C(2)) * V_eff(n, x));
  }

  static Real sample_activation(Real z);
  static Real sample_mu(Real x);
  static Real sample_gamma(Real t);
  static Real sample_v(Real _x);
  static Real sample_N(Real x);
  static inline const Real sample_mass = Real::from_z(INT64_C(3));
  static inline const Real sample_time = Real::from_z(INT64_C(2));
  static Real density_radicand_at(uint64_t n);
  static bool static_time_nonnegative_at(uint64_t n);
  static bool density_radicand_nonnegative_at(uint64_t n);
  static Real density_value_at(uint64_t n);
  static bool density_value_nonnegative_at(uint64_t n);
  static bool massive_potential_nonnegative_at(uint64_t n);
  static inline const bool sample_static_nonneg =
      static_time_nonnegative_at(UINT64_C(1));
  static inline const bool sample_density_radicand_nonneg =
      density_radicand_nonnegative_at(UINT64_C(1));
  static inline const bool sample_density_value_nonneg =
      density_value_nonnegative_at(UINT64_C(1));
  static inline const bool sample_massive_nonneg =
      massive_potential_nonnegative_at(UINT64_C(2));
};

#endif // INCLUDED_DENSITY_POTENTIAL_TRACE
