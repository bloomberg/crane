#include "fold_sequence_state_trace.h"

FoldSequenceStateTraceCase::Line
FoldSequenceStateTraceCase::line_through(std::pair<Real, Real> p1,
                                         std::pair<Real, Real> p2) {
  auto [x1, y1] = std::move(p1);
  auto [x2, y2] = std::move(p2);
  if ((x1 == x2)) {
    return Line{Real::from_z(INT64_C(1)), Real::from_z(INT64_C(0)),
                (-std::move(x1))};
  } else {
    Real a = (y1 - y2);
    Real b = (x2 - x1);
    Real c =
        ((std::move(x1) * std::move(y2)) - (std::move(x2) * std::move(y1)));
    return Line{std::move(a), std::move(b), std::move(c)};
  }
}

FoldSequenceStateTraceCase::Line
FoldSequenceStateTraceCase::perp_bisector(std::pair<Real, Real> p1,
                                          std::pair<Real, Real> p2) {
  auto [x1, y1] = std::move(p1);
  auto [x2, y2] = std::move(p2);
  if ((x1 == x2)) {
    if ((y1 == y2)) {
      return Line{Real::from_z(INT64_C(1)), Real::from_z(INT64_C(0)),
                  (-std::move(x1))};
    } else {
      Real a = Real::from_z(INT64_C(0));
      Real b = (Real::from_z(INT64_C(2)) * (y2 - y1));
      Real c = ((((x1 * x1) + (y1 * y1)) - (x2 * x2)) - (y2 * y2));
      return Line{std::move(a), std::move(b), std::move(c)};
    }
  } else {
    Real a = (Real::from_z(INT64_C(2)) * (x2 - x1));
    Real b = (Real::from_z(INT64_C(2)) * (y2 - y1));
    Real c = ((((x1 * x1) + (y1 * y1)) - (x2 * x2)) - (y2 * y2));
    return Line{std::move(a), std::move(b), std::move(c)};
  }
}

FoldSequenceStateTraceCase::Line FoldSequenceStateTraceCase::perp_through(
    std::pair<Real, Real> p, const FoldSequenceStateTraceCase::Line &l) {
  auto [x, y] = std::move(p);
  Real c = ((l.A * std::move(y)) - (l.B * std::move(x)));
  return Line{l.B, (-l.A), std::move(c)};
}

FoldSequenceStateTraceCase::Fold
FoldSequenceStateTraceCase::fold_O1(std::pair<Real, Real> p1,
                                    std::pair<Real, Real> p2) {
  return Fold::fold_line_ctor(line_through(std::move(p1), std::move(p2)));
}

FoldSequenceStateTraceCase::Fold
FoldSequenceStateTraceCase::fold_O2(std::pair<Real, Real> p1,
                                    std::pair<Real, Real> p2) {
  return Fold::fold_line_ctor(perp_bisector(std::move(p1), std::move(p2)));
}

FoldSequenceStateTraceCase::Fold
FoldSequenceStateTraceCase::fold_O4(std::pair<Real, Real> p,
                                    const FoldSequenceStateTraceCase::Line &l) {
  return Fold::fold_line_ctor(perp_through(std::move(p), l));
}

FoldSequenceStateTraceCase::ConstructionState
FoldSequenceStateTraceCase::add_fold_to_state(
    const FoldSequenceStateTraceCase::ConstructionState &st,
    const FoldSequenceStateTraceCase::FoldStep &step) {
  FoldSequenceStateTraceCase::Line new_line = step.execute_fold_step();
  return ConstructionState{st.state_points,
                           List<FoldSequenceStateTraceCase::Line>::cons(
                               std::move(new_line), st.state_lines)};
}

FoldSequenceStateTraceCase::ConstructionState
FoldSequenceStateTraceCase::execute_sequence(
    FoldSequenceStateTraceCase::ConstructionState st,
    const List<FoldSequenceStateTraceCase::FoldStep> &seq) {
  if (std::holds_alternative<
          typename List<FoldSequenceStateTraceCase::FoldStep>::Nil>(seq.v())) {
    return st;
  } else {
    const auto &[a0, a1] =
        std::get<typename List<FoldSequenceStateTraceCase::FoldStep>::Cons>(
            seq.v());
    return execute_sequence(add_fold_to_state(std::move(st), a0), *a1);
  }
}

uint64_t FoldSequenceStateTraceCase::line_count_after_sample_sequence(
    FoldSequenceStateTraceCase::ConstructionState st) {
  return execute_sequence(std::move(st), sample_sequence).state_lines.length();
}
