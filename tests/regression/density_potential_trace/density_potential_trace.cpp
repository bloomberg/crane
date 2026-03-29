#include <density_potential_trace.h>

#include <crane_real.h>
#include <cstdint>
#include <type_traits>

__attribute__((pure)) Real
DensityPotentialTraceCase::sample_activation(const Real z) {
  return z;
}

__attribute__((pure)) Real DensityPotentialTraceCase::sample_mu(const Real x) {
  return r_inv((Real::from_z(static_cast<int64_t>(1u)) + (x * x)));
}

__attribute__((pure)) Real
DensityPotentialTraceCase::sample_gamma(const Real t) {
  return (t / Real::from_z(static_cast<int64_t>((2u * 1u))));
}

__attribute__((pure)) Real DensityPotentialTraceCase::sample_v(const Real _x) {
  return r_inv(Real::from_z(static_cast<int64_t>((2u * (2u * 1u)))));
}

__attribute__((pure)) Real DensityPotentialTraceCase::sample_N(const Real x) {
  return (Real::from_z(static_cast<int64_t>(1u)) + (x * x));
}

__attribute__((pure)) Real
DensityPotentialTraceCase::density_radicand_at(const unsigned int n) {
  Real t = Real::from_nat(n);
  return (r_pow(lapse(sample_activation, sample_mu, sample_gamma(t)), 2u) -
          r_pow(sample_v(t), 2u));
}

__attribute__((pure)) bool
DensityPotentialTraceCase::static_time_nonnegative_at(const unsigned int n) {
  if ((Real::from_z(INT64_C(0)) <=
       proper_time_static(sample_activation, sample_mu, Real::from_nat(n),
                          sample_time))) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool
DensityPotentialTraceCase::density_radicand_nonnegative_at(
    const unsigned int n) {
  if ((Real::from_z(INT64_C(0)) <= density_radicand_at(n))) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) Real
DensityPotentialTraceCase::density_value_at(const unsigned int n) {
  return proper_time_density_path(sample_activation, sample_mu, sample_gamma,
                                  sample_v, Real::from_nat(n));
}

__attribute__((pure)) bool
DensityPotentialTraceCase::density_value_nonnegative_at(const unsigned int n) {
  if ((Real::from_z(INT64_C(0)) <= density_value_at(n))) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool
DensityPotentialTraceCase::massive_potential_nonnegative_at(
    const unsigned int n) {
  if ((Real::from_z(INT64_C(0)) <=
       V_eff_massive(sample_N, sample_mass, Real::from_nat(n)))) {
    return true;
  } else {
    return false;
  }
}
