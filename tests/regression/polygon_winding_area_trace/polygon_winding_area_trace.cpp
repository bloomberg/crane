#include <polygon_winding_area_trace.h>

int64_t BinInt::pow_pos(const int64_t &z, unsigned int _x0) {
  return Pos::template iter<int64_t>(
      [=](int64_t _x0) mutable -> int64_t { return (z * _x0); }, INT64_C(1),
      _x0);
}

Real PolygonWindingAreaTraceCase::hav(const Real theta) {
  return r_sqr(r_sin((theta / Real::from_z(INT64_C(2)))));
}

Real PolygonWindingAreaTraceCase::distance(
    const PolygonWindingAreaTraceCase::Point &p1,
    const PolygonWindingAreaTraceCase::Point &p2) {
  Real dphi = (p2.phi - p1.phi);
  Real dlambda = (p2.lambda - p1.lambda);
  Real a = (hav(dphi) + ((r_cos(p1.phi) * r_cos(p2.phi)) * hav(dlambda)));
  return ((Real::from_z(INT64_C(2)) * R_earth) * r_asin(r_sqrt(a)));
}

Real PolygonWindingAreaTraceCase::lon_diff(const Real lon1, const Real lon2) {
  Real raw = (lon2 - lon1);
  if ((Real::pi() < raw)) {
    return (raw - (Real::from_z(INT64_C(2)) * Real::pi()));
  } else {
    if ((raw < (-Real::pi()))) {
      return (raw + (Real::from_z(INT64_C(2)) * Real::pi()));
    } else {
      return raw;
    }
  }
}

Real PolygonWindingAreaTraceCase::spherical_shoelace_aux(
    const List<PolygonWindingAreaTraceCase::Point> &pts,
    const List<PolygonWindingAreaTraceCase::Point> &all_pts,
    const unsigned int &idx) {
  if (std::holds_alternative<
          typename List<PolygonWindingAreaTraceCase::Point>::Nil>(pts.v())) {
    return Real::from_z(INT64_C(0));
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<PolygonWindingAreaTraceCase::Point>::Cons>(
            pts.v());
    unsigned int n = all_pts.length();
    Real lambda_prev =
        nth_cyclic<PolygonWindingAreaTraceCase::Point>(
            d_a0, all_pts,
            ((((idx + n) - 1u) > (idx + n) ? 0 : ((idx + n) - 1u))))
            .lambda;
    Real lambda_next = nth_cyclic<PolygonWindingAreaTraceCase::Point>(
                           d_a0, all_pts, (idx + 1u))
                           .lambda;
    Real term = (lon_diff(lambda_prev, lambda_next) * r_sin(d_a0.phi));
    return (term + spherical_shoelace_aux(*(d_a1), all_pts, (idx + 1u)));
  }
}

Real PolygonWindingAreaTraceCase::spherical_shoelace(
    const List<PolygonWindingAreaTraceCase::Point> &pts) {
  return spherical_shoelace_aux(pts, pts, 0u);
}

Real PolygonWindingAreaTraceCase::spherical_polygon_area(
    const List<PolygonWindingAreaTraceCase::Point> &poly) {
  return r_abs(
      ((r_sqr(R_earth) * spherical_shoelace(poly)) / Real::from_z(INT64_C(2))));
}

Real PolygonWindingAreaTraceCase::distance_to_central_angle(const Real d) {
  return (d / R_earth);
}

Real PolygonWindingAreaTraceCase::spherical_cosine_arg(const Real ca,
                                                       const Real cb,
                                                       const Real cab) {
  Real num = (r_cos(cab) - (r_cos(ca) * r_cos(cb)));
  Real denom = (r_sin(ca) * r_sin(cb));
  return r_max(
      Real::from_z(INT64_C(-1)),
      r_min(Real::from_z(INT64_C(1)),
            (num / r_max(r_abs(denom),
                         (Real::from_z(INT64_C(1)) /
                          Real::from_z(BinInt::pow_pos(
                              INT64_C(10), (2u * (2u * (2u * 1u) + 1u)))))))));
}

Real PolygonWindingAreaTraceCase::law_of_cosines_arg(const Real da,
                                                     const Real db,
                                                     const Real dab) {
  Real ca = distance_to_central_angle(da);
  Real cb = distance_to_central_angle(db);
  Real cab = distance_to_central_angle(dab);
  return spherical_cosine_arg(ca, cb, cab);
}

Real PolygonWindingAreaTraceCase::segment_angle(
    const PolygonWindingAreaTraceCase::Point &p,
    const PolygonWindingAreaTraceCase::Point &a,
    const PolygonWindingAreaTraceCase::Point &b) {
  Real da = distance(p, a);
  Real db = distance(p, b);
  Real dab = distance(a, b);
  return r_acos(law_of_cosines_arg(da, db, dab));
}

Real PolygonWindingAreaTraceCase::winding_sum_aux(
    const PolygonWindingAreaTraceCase::Point &p,
    const List<PolygonWindingAreaTraceCase::Point> &pts,
    const PolygonWindingAreaTraceCase::Point &first) {
  if (std::holds_alternative<
          typename List<PolygonWindingAreaTraceCase::Point>::Nil>(pts.v())) {
    return Real::from_z(INT64_C(0));
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<PolygonWindingAreaTraceCase::Point>::Cons>(
            pts.v());
    auto &&_sv0 = *(d_a1);
    if (std::holds_alternative<
            typename List<PolygonWindingAreaTraceCase::Point>::Nil>(_sv0.v())) {
      return segment_angle(p, d_a0, first);
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<PolygonWindingAreaTraceCase::Point>::Cons>(
              _sv0.v());
      return (segment_angle(p, d_a0, d_a00) +
              winding_sum_aux(p, *(d_a1), first));
    }
  }
}

Real PolygonWindingAreaTraceCase::winding_sum(
    const PolygonWindingAreaTraceCase::Point &p,
    const List<PolygonWindingAreaTraceCase::Point> &poly) {
  if (std::holds_alternative<
          typename List<PolygonWindingAreaTraceCase::Point>::Nil>(poly.v())) {
    return Real::from_z(INT64_C(0));
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<PolygonWindingAreaTraceCase::Point>::Cons>(
            poly.v());
    return winding_sum_aux(p, poly, d_a0);
  }
}

Real PolygonWindingAreaTraceCase::winding_number(
    const PolygonWindingAreaTraceCase::Point &p,
    const List<PolygonWindingAreaTraceCase::Point> &poly) {
  return (winding_sum(p, poly) / (Real::from_z(INT64_C(2)) * Real::pi()));
}

bool PolygonWindingAreaTraceCase::inside_by_winding(
    const PolygonWindingAreaTraceCase::Point &p,
    const List<PolygonWindingAreaTraceCase::Point> &poly) {
  if ((Real::pi() < winding_sum(p, poly))) {
    return true;
  } else {
    return false;
  }
}

bool PolygonWindingAreaTraceCase::nonnegative_area(
    const List<PolygonWindingAreaTraceCase::Point> &poly) {
  if ((Real::from_z(INT64_C(0)) <= spherical_polygon_area(poly))) {
    return true;
  } else {
    return false;
  }
}

bool PolygonWindingAreaTraceCase::nonnegative_segment_angle(
    const PolygonWindingAreaTraceCase::Point &p,
    const PolygonWindingAreaTraceCase::Point &a,
    const PolygonWindingAreaTraceCase::Point &b) {
  if ((Real::from_z(INT64_C(0)) <= segment_angle(p, a, b))) {
    return true;
  } else {
    return false;
  }
}

bool PolygonWindingAreaTraceCase::winding_number_gt_half(
    const PolygonWindingAreaTraceCase::Point &p,
    const List<PolygonWindingAreaTraceCase::Point> &poly) {
  if (((Real::from_z(INT64_C(1)) / Real::from_z(INT64_C(2))) <
       winding_number(p, poly))) {
    return true;
  } else {
    return false;
  }
}

PolygonWindingAreaTraceCase::Polygon
PolygonWindingAreaTraceCase::test_equatorial_square(const Real delta) {
  return List<PolygonWindingAreaTraceCase::Point>::cons(
      Point{Real::from_z(INT64_C(0)), Real::from_z(INT64_C(0))},
      List<PolygonWindingAreaTraceCase::Point>::cons(
          Point{Real::from_z(INT64_C(0)), delta},
          List<PolygonWindingAreaTraceCase::Point>::cons(
              Point{delta, delta},
              List<PolygonWindingAreaTraceCase::Point>::cons(
                  Point{delta, Real::from_z(INT64_C(0))},
                  List<PolygonWindingAreaTraceCase::Point>::nil()))));
}

Real Rdefinitions::Q2R(const Q &x) {
  return (Real::from_z(x.Qnum) *
          r_inv(Real::from_z(static_cast<int64_t>(x.Qden))));
}
