#include <fold_sequence_state_trace.h>

#include <crane_real.h>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool PeanoNat::eqb(const unsigned int n,
                                         const unsigned int m) {
  if (n <= 0) {
    if (m <= 0) {
      return true;
    } else {
      unsigned int _x = m - 1;
      return false;
    }
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int m_ = m - 1;
      return PeanoNat::eqb(n_, m_);
    }
  }
}

std::shared_ptr<FoldSequenceStateTraceCase::Line>
FoldSequenceStateTraceCase::line_through(const std::pair<Real, Real> p1,
                                         const std::pair<Real, Real> p2) {
  Real x1 = p1.first;
  Real y1 = p1.second;
  Real x2 = p2.first;
  Real y2 = p2.second;
  if ((x1 == x2)) {
    return std::make_shared<FoldSequenceStateTraceCase::Line>(
        Line{Real::from_z(static_cast<int64_t>(1u)), Real::from_z(INT64_C(0)),
             (-x1)});
  } else {
    Real a = (y1 - y2);
    Real b = (x2 - x1);
    Real c = ((x1 * y2) - (x2 * y1));
    return std::make_shared<FoldSequenceStateTraceCase::Line>(Line{a, b, c});
  }
}

std::shared_ptr<FoldSequenceStateTraceCase::Line>
FoldSequenceStateTraceCase::perp_bisector(const std::pair<Real, Real> p1,
                                          const std::pair<Real, Real> p2) {
  Real x1 = p1.first;
  Real y1 = p1.second;
  Real x2 = p2.first;
  Real y2 = p2.second;
  if ((x1 == x2)) {
    if ((y1 == y2)) {
      return std::make_shared<FoldSequenceStateTraceCase::Line>(
          Line{Real::from_z(static_cast<int64_t>(1u)), Real::from_z(INT64_C(0)),
               (-x1)});
    } else {
      Real a = Real::from_z(INT64_C(0));
      Real b = (Real::from_z(static_cast<int64_t>((2u * 1u))) * (y2 - y1));
      Real c = ((((x1 * x1) + (y1 * y1)) - (x2 * x2)) - (y2 * y2));
      return std::make_shared<FoldSequenceStateTraceCase::Line>(Line{a, b, c});
    }
  } else {
    Real a = (Real::from_z(static_cast<int64_t>((2u * 1u))) * (x2 - x1));
    Real b = (Real::from_z(static_cast<int64_t>((2u * 1u))) * (y2 - y1));
    Real c = ((((x1 * x1) + (y1 * y1)) - (x2 * x2)) - (y2 * y2));
    return std::make_shared<FoldSequenceStateTraceCase::Line>(Line{a, b, c});
  }
}

std::shared_ptr<FoldSequenceStateTraceCase::Line>
FoldSequenceStateTraceCase::perp_through(
    const std::pair<Real, Real> p,
    std::shared_ptr<FoldSequenceStateTraceCase::Line> l) {
  Real x = p.first;
  Real y = p.second;
  Real c = ((l->A * std::move(y)) - (l->B * x));
  return std::make_shared<FoldSequenceStateTraceCase::Line>(
      Line{l->B, (-l->A), c});
}

std::shared_ptr<FoldSequenceStateTraceCase::Fold>
FoldSequenceStateTraceCase::fold_O1(const std::pair<Real, Real> p1,
                                    const std::pair<Real, Real> p2) {
  return Fold::fold_line_ctor(line_through(p1, p2));
}

std::shared_ptr<FoldSequenceStateTraceCase::Fold>
FoldSequenceStateTraceCase::fold_O2(const std::pair<Real, Real> p1,
                                    const std::pair<Real, Real> p2) {
  return Fold::fold_line_ctor(perp_bisector(p1, p2));
}

std::shared_ptr<FoldSequenceStateTraceCase::Fold>
FoldSequenceStateTraceCase::fold_O4(
    const std::pair<Real, Real> p,
    std::shared_ptr<FoldSequenceStateTraceCase::Line> l) {
  return Fold::fold_line_ctor(perp_through(p, l));
}

std::shared_ptr<FoldSequenceStateTraceCase::ConstructionState>
FoldSequenceStateTraceCase::add_fold_to_state(
    std::shared_ptr<FoldSequenceStateTraceCase::ConstructionState> st,
    const std::shared_ptr<FoldSequenceStateTraceCase::FoldStep> &step) {
  std::shared_ptr<FoldSequenceStateTraceCase::Line> new_line =
      step->execute_fold_step();
  return std::make_shared<FoldSequenceStateTraceCase::ConstructionState>(
      ConstructionState{
          st->state_points,
          List<std::shared_ptr<FoldSequenceStateTraceCase::Line>>::cons(
              new_line, st->state_lines)});
}

std::shared_ptr<FoldSequenceStateTraceCase::ConstructionState>
FoldSequenceStateTraceCase::execute_sequence(
    std::shared_ptr<FoldSequenceStateTraceCase::ConstructionState> st,
    const std::shared_ptr<
        List<std::shared_ptr<FoldSequenceStateTraceCase::FoldStep>>> &seq) {
  return std::visit(
      Overloaded{
          [&](const typename List<
              std::shared_ptr<FoldSequenceStateTraceCase::FoldStep>>::Nil _args)
              -> std::shared_ptr<
                  FoldSequenceStateTraceCase::ConstructionState> {
            return std::move(st);
          },
          [&](const typename List<std::shared_ptr<
                  FoldSequenceStateTraceCase::FoldStep>>::Cons _args)
              -> std::shared_ptr<
                  FoldSequenceStateTraceCase::ConstructionState> {
            return execute_sequence(
                add_fold_to_state(std::move(st), _args.d_a0), _args.d_a1);
          }},
      seq->v());
}

__attribute__((pure)) unsigned int
FoldSequenceStateTraceCase::line_count_after_sample_sequence(
    const std::shared_ptr<FoldSequenceStateTraceCase::ConstructionState> &st) {
  return execute_sequence(st, sample_sequence)->state_lines->length();
}
