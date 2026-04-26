#include <fold_sequence_state_trace.h>

#include <crane_real.h>
#include <cstdint>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) FoldSequenceStateTraceCase::Line
FoldSequenceStateTraceCase::line_through(const std::pair<Real, Real> &p1,
                                         const std::pair<Real, Real> &p2) {
  const Real &x1 = p1.first;
  const Real &y1 = p1.second;
  const Real &x2 = p2.first;
  const Real &y2 = p2.second;
  if ((x1 == x2)) {
    return Line{Real::from_z(INT64_C(1)), Real::from_z(INT64_C(0)), (-x1)};
  } else {
    Real a = (y1 - y2);
    Real b = (x2 - x1);
    Real c = ((x1 * y2) - (x2 * y1));
    return Line{a, b, c};
  }
}

__attribute__((pure)) FoldSequenceStateTraceCase::Line
FoldSequenceStateTraceCase::perp_bisector(const std::pair<Real, Real> &p1,
                                          const std::pair<Real, Real> &p2) {
  const Real &x1 = p1.first;
  const Real &y1 = p1.second;
  const Real &x2 = p2.first;
  const Real &y2 = p2.second;
  if ((x1 == x2)) {
    if ((y1 == y2)) {
      return Line{Real::from_z(INT64_C(1)), Real::from_z(INT64_C(0)), (-x1)};
    } else {
      Real a = Real::from_z(INT64_C(0));
      Real b = (Real::from_z(INT64_C(2)) * (y2 - y1));
      Real c = ((((x1 * x1) + (y1 * y1)) - (x2 * x2)) - (y2 * y2));
      return Line{a, b, c};
    }
  } else {
    Real a = (Real::from_z(INT64_C(2)) * (x2 - x1));
    Real b = (Real::from_z(INT64_C(2)) * (y2 - y1));
    Real c = ((((x1 * x1) + (y1 * y1)) - (x2 * x2)) - (y2 * y2));
    return Line{a, b, c};
  }
}

__attribute__((pure)) FoldSequenceStateTraceCase::Line
FoldSequenceStateTraceCase::perp_through(
    const std::pair<Real, Real> &p, const FoldSequenceStateTraceCase::Line &l) {
  const Real &x = p.first;
  const Real &y = p.second;
  Real c = ((l.A * y) - (l.B * x));
  return Line{l.B, (-l.A), c};
}

__attribute__((pure)) FoldSequenceStateTraceCase::Fold
FoldSequenceStateTraceCase::fold_O1(const std::pair<Real, Real> &p1,
                                    const std::pair<Real, Real> &p2) {
  return Fold::fold_line_ctor(line_through(p1, p2));
}

__attribute__((pure)) FoldSequenceStateTraceCase::Fold
FoldSequenceStateTraceCase::fold_O2(const std::pair<Real, Real> &p1,
                                    const std::pair<Real, Real> &p2) {
  return Fold::fold_line_ctor(perp_bisector(p1, p2));
}

__attribute__((pure)) FoldSequenceStateTraceCase::Fold
FoldSequenceStateTraceCase::fold_O4(const std::pair<Real, Real> &p,
                                    const FoldSequenceStateTraceCase::Line &l) {
  return Fold::fold_line_ctor(perp_through(p, l));
}

__attribute__((pure)) FoldSequenceStateTraceCase::ConstructionState
FoldSequenceStateTraceCase::add_fold_to_state(
    const FoldSequenceStateTraceCase::ConstructionState &st,
    const FoldSequenceStateTraceCase::FoldStep &step) {
  FoldSequenceStateTraceCase::Line new_line = step.execute_fold_step();
  return ConstructionState{
      st.state_points,
      List<FoldSequenceStateTraceCase::Line>::cons(new_line, st.state_lines)};
}

__attribute__((pure)) FoldSequenceStateTraceCase::ConstructionState
FoldSequenceStateTraceCase::execute_sequence(
    FoldSequenceStateTraceCase::ConstructionState st,
    const List<FoldSequenceStateTraceCase::FoldStep> &seq) {
  if (std::holds_alternative<
          typename List<FoldSequenceStateTraceCase::FoldStep>::Nil>(seq.v())) {
    return st;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<FoldSequenceStateTraceCase::FoldStep>::Cons>(
            seq.v());
    return execute_sequence(add_fold_to_state(st, d_a0), *(d_a1));
  }
}

__attribute__((pure)) unsigned int
FoldSequenceStateTraceCase::line_count_after_sample_sequence(
    const FoldSequenceStateTraceCase::ConstructionState &st) {
  return execute_sequence(st, sample_sequence).state_lines.length();
}
