#include "density_potential_trace.h"

Real DensityPotentialTraceCase::sample_activation(Real z) { return z; }

Real DensityPotentialTraceCase::sample_mu(Real x) {
  return r_inv((Real::from_z(INT64_C(1)) + (x * x)));
}

Real DensityPotentialTraceCase::sample_gamma(Real t) {
  return (t / Real::from_z(INT64_C(2)));
}

Real DensityPotentialTraceCase::sample_v(Real) {
  return r_inv(Real::from_z(INT64_C(4)));
}

Real DensityPotentialTraceCase::sample_N(Real x) {
  return (Real::from_z(INT64_C(1)) + (x * x));
}

Real DensityPotentialTraceCase::density_radicand_at(uint64_t n) {
  Real t = Real::from_nat(n);
  return (
      r_pow(lapse(sample_activation, sample_mu, sample_gamma(t)), UINT64_C(2)) -
      r_pow(sample_v(t), UINT64_C(2)));
}

bool DensityPotentialTraceCase::static_time_nonnegative_at(uint64_t n) {
  if ((Real::from_z(INT64_C(0)) <=
       proper_time_static(sample_activation, sample_mu, Real::from_nat(n),
                          sample_time))) {
    return true;
  } else {
    return false;
  }
}

bool DensityPotentialTraceCase::density_radicand_nonnegative_at(uint64_t n) {
  if ((Real::from_z(INT64_C(0)) <= density_radicand_at(n))) {
    return true;
  } else {
    return false;
  }
}

Real DensityPotentialTraceCase::density_value_at(uint64_t n) {
  return proper_time_density_path(sample_activation, sample_mu, sample_gamma,
                                  sample_v, Real::from_nat(n));
}

bool DensityPotentialTraceCase::density_value_nonnegative_at(uint64_t n) {
  if ((Real::from_z(INT64_C(0)) <= density_value_at(n))) {
    return true;
  } else {
    return false;
  }
}

bool DensityPotentialTraceCase::massive_potential_nonnegative_at(uint64_t n) {
  if ((Real::from_z(INT64_C(0)) <=
       V_eff_massive(sample_N, sample_mass, Real::from_nat(n)))) {
    return true;
  } else {
    return false;
  }
}
