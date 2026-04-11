#include <polygon_winding_area_trace.h>

#include <crane_real.h>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) int64_t BinInt::pow_pos(const int64_t z,
                                              const unsigned int _x0) {
  return Pos::template iter<int64_t>(
      [=](int64_t _x0) mutable -> int64_t { return (z * _x0); }, INT64_C(1),
      _x0);
}

__attribute__((pure)) Real PolygonWindingAreaTraceCase::hav(const Real theta) {
  return r_sqr(r_sin((theta / Real::from_z(INT64_C(2)))));
}

__attribute__((pure)) Real PolygonWindingAreaTraceCase::distance(
    const std::shared_ptr<PolygonWindingAreaTraceCase::Point> &p1,
    const std::shared_ptr<PolygonWindingAreaTraceCase::Point> &p2) {
  Real dphi = (p2->phi - p1->phi);
  Real dlambda = (p2->lambda - p1->lambda);
  Real a = (hav(dphi) + ((r_cos(p1->phi) * r_cos(p2->phi)) * hav(dlambda)));
  return ((Real::from_z(INT64_C(2)) * R_earth) * r_asin(r_sqrt(a)));
}

__attribute__((pure)) Real
PolygonWindingAreaTraceCase::lon_diff(const Real lon1, const Real lon2) {
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

__attribute__((pure)) Real PolygonWindingAreaTraceCase::spherical_shoelace_aux(
    const std::shared_ptr<
        List<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>> &pts,
    const std::shared_ptr<
        List<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>> &all_pts,
    const unsigned int idx) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<PolygonWindingAreaTraceCase::Point>>::Nil)
              -> Real { return Real::from_z(INT64_C(0)); },
          [&](const typename List<
              std::shared_ptr<PolygonWindingAreaTraceCase::Point>>::Cons _args)
              -> Real {
            unsigned int n = all_pts->length();
            Real lambda_prev =
                nth_cyclic<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>(
                    _args.d_a0, all_pts,
                    ((((idx + n) - 1u) > (idx + n) ? 0 : ((idx + n) - 1u))))
                    ->lambda;
            Real lambda_next =
                nth_cyclic<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>(
                    _args.d_a0, all_pts, (idx + 1u))
                    ->lambda;
            Real term =
                (lon_diff(lambda_prev, lambda_next) * r_sin(_args.d_a0->phi));
            return (term +
                    spherical_shoelace_aux(_args.d_a1, all_pts, (idx + 1u)));
          }},
      pts->v());
}

__attribute__((pure)) Real PolygonWindingAreaTraceCase::spherical_shoelace(
    const std::shared_ptr<
        List<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>> &pts) {
  return spherical_shoelace_aux(pts, pts, 0u);
}

__attribute__((pure)) Real PolygonWindingAreaTraceCase::spherical_polygon_area(
    const std::shared_ptr<
        List<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>> &poly) {
  return r_abs(
      ((r_sqr(R_earth) * spherical_shoelace(poly)) / Real::from_z(INT64_C(2))));
}

__attribute__((pure)) Real
PolygonWindingAreaTraceCase::distance_to_central_angle(const Real d) {
  return (d / R_earth);
}

__attribute__((pure)) Real PolygonWindingAreaTraceCase::spherical_cosine_arg(
    const Real ca, const Real cb, const Real cab) {
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

__attribute__((pure)) Real PolygonWindingAreaTraceCase::law_of_cosines_arg(
    const Real da, const Real db, const Real dab) {
  Real ca = distance_to_central_angle(da);
  Real cb = distance_to_central_angle(db);
  Real cab = distance_to_central_angle(dab);
  return spherical_cosine_arg(ca, cb, cab);
}

__attribute__((pure)) Real PolygonWindingAreaTraceCase::segment_angle(
    const std::shared_ptr<PolygonWindingAreaTraceCase::Point> &p,
    const std::shared_ptr<PolygonWindingAreaTraceCase::Point> &a,
    const std::shared_ptr<PolygonWindingAreaTraceCase::Point> &b) {
  Real da = distance(p, a);
  Real db = distance(p, b);
  Real dab = distance(a, b);
  return r_acos(law_of_cosines_arg(da, db, dab));
}

__attribute__((pure)) Real PolygonWindingAreaTraceCase::winding_sum_aux(
    const std::shared_ptr<PolygonWindingAreaTraceCase::Point> &p,
    const std::shared_ptr<
        List<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>> &pts,
    const std::shared_ptr<PolygonWindingAreaTraceCase::Point> &first) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<PolygonWindingAreaTraceCase::Point>>::Nil)
              -> Real { return Real::from_z(INT64_C(0)); },
          [&](const typename List<
              std::shared_ptr<PolygonWindingAreaTraceCase::Point>>::Cons _args)
              -> Real {
            return std::visit(
                Overloaded{
                    [&](const typename List<std::shared_ptr<
                            PolygonWindingAreaTraceCase::Point>>::Nil) -> Real {
                      return segment_angle(p, _args.d_a0, first);
                    },
                    [&](const typename List<std::shared_ptr<
                            PolygonWindingAreaTraceCase::Point>>::Cons _args0)
                        -> Real {
                      return (segment_angle(p, _args.d_a0, _args0.d_a0) +
                              winding_sum_aux(p, _args.d_a1, first));
                    }},
                _args.d_a1->v());
          }},
      pts->v());
}

__attribute__((pure)) Real PolygonWindingAreaTraceCase::winding_sum(
    const std::shared_ptr<PolygonWindingAreaTraceCase::Point> &p,
    const std::shared_ptr<
        List<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>> &poly) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<PolygonWindingAreaTraceCase::Point>>::Nil)
              -> Real { return Real::from_z(INT64_C(0)); },
          [&](const typename List<
              std::shared_ptr<PolygonWindingAreaTraceCase::Point>>::Cons _args)
              -> Real { return winding_sum_aux(p, poly, _args.d_a0); }},
      poly->v());
}

__attribute__((pure)) Real PolygonWindingAreaTraceCase::winding_number(
    const std::shared_ptr<PolygonWindingAreaTraceCase::Point> &p,
    const std::shared_ptr<
        List<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>> &poly) {
  return (winding_sum(p, poly) / (Real::from_z(INT64_C(2)) * Real::pi()));
}

__attribute__((pure)) bool PolygonWindingAreaTraceCase::inside_by_winding(
    const std::shared_ptr<PolygonWindingAreaTraceCase::Point> &p,
    const std::shared_ptr<
        List<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>> &poly) {
  if ((Real::pi() < winding_sum(p, poly))) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool PolygonWindingAreaTraceCase::nonnegative_area(
    const std::shared_ptr<
        List<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>> &poly) {
  if ((Real::from_z(INT64_C(0)) <= spherical_polygon_area(poly))) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool
PolygonWindingAreaTraceCase::nonnegative_segment_angle(
    const std::shared_ptr<PolygonWindingAreaTraceCase::Point> &p,
    const std::shared_ptr<PolygonWindingAreaTraceCase::Point> &a,
    const std::shared_ptr<PolygonWindingAreaTraceCase::Point> &b) {
  if ((Real::from_z(INT64_C(0)) <= segment_angle(p, a, b))) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool PolygonWindingAreaTraceCase::winding_number_gt_half(
    const std::shared_ptr<PolygonWindingAreaTraceCase::Point> &p,
    const std::shared_ptr<
        List<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>> &poly) {
  if (((Real::from_z(INT64_C(1)) / Real::from_z(INT64_C(2))) <
       winding_number(p, poly))) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) PolygonWindingAreaTraceCase::Polygon
PolygonWindingAreaTraceCase::test_equatorial_square(const Real delta) {
  return List<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>::cons(
      std::make_shared<PolygonWindingAreaTraceCase::Point>(
          Point{Real::from_z(INT64_C(0)), Real::from_z(INT64_C(0))}),
      List<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>::cons(
          std::make_shared<PolygonWindingAreaTraceCase::Point>(
              Point{Real::from_z(INT64_C(0)), delta}),
          List<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>::cons(
              std::make_shared<PolygonWindingAreaTraceCase::Point>(
                  Point{delta, delta}),
              List<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>::cons(
                  std::make_shared<PolygonWindingAreaTraceCase::Point>(
                      Point{delta, Real::from_z(INT64_C(0))}),
                  List<std::shared_ptr<PolygonWindingAreaTraceCase::Point>>::
                      nil()))));
}

__attribute__((pure)) Real Rdefinitions::Q2R(std::shared_ptr<Q> x) {
  return (Real::from_z(x->Qnum) *
          r_inv(Real::from_z(static_cast<int64_t>(x->Qden))));
}
