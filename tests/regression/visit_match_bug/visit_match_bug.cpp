#include <visit_match_bug.h>

VisitMatchBug::Tree VisitMatchBug::consume(VisitMatchBug::Tree t) { return t; }

unsigned int VisitMatchBug::match_after_consume(const VisitMatchBug::Tree &t) {
  VisitMatchBug::Tree t2 = consume(t);
  if (std::holds_alternative<typename VisitMatchBug::Tree::Leaf>(t2.v_mut())) {
    auto &[d_a0] = std::get<typename VisitMatchBug::Tree::Leaf>(t2.v_mut());
    return d_a0;
  } else {
    auto &[d_a0, d_a1, d_a2] =
        std::get<typename VisitMatchBug::Tree::Node>(t2.v_mut());
    return d_a1;
  }
}

unsigned int VisitMatchBug::match_last_use(const VisitMatchBug::Tree &t) {
  if (std::holds_alternative<typename VisitMatchBug::Tree::Leaf>(t.v())) {
    const auto &[d_a0] = std::get<typename VisitMatchBug::Tree::Leaf>(t.v());
    return d_a0;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename VisitMatchBug::Tree::Node>(t.v());
    return d_a1;
  }
}

unsigned int VisitMatchBug::nested_match_consume(const VisitMatchBug::Tree &t) {
  VisitMatchBug::Tree t2 = consume(t);
  if (std::holds_alternative<typename VisitMatchBug::Tree::Leaf>(t2.v_mut())) {
    auto &[d_a0] = std::get<typename VisitMatchBug::Tree::Leaf>(t2.v_mut());
    return d_a0;
  } else {
    auto &[d_a0, d_a1, d_a2] =
        std::get<typename VisitMatchBug::Tree::Node>(t2.v_mut());
    return d_a1;
  }
}

unsigned int VisitMatchBug::chain_then_match(const VisitMatchBug::Tree &t1) {
  VisitMatchBug::Tree t2 = consume(t1);
  VisitMatchBug::Tree t3 = consume(std::move(t2));
  if (std::holds_alternative<typename VisitMatchBug::Tree::Leaf>(t3.v_mut())) {
    auto &[d_a0] = std::get<typename VisitMatchBug::Tree::Leaf>(t3.v_mut());
    return d_a0;
  } else {
    auto &[d_a0, d_a1, d_a2] =
        std::get<typename VisitMatchBug::Tree::Node>(t3.v_mut());
    return d_a1;
  }
}

unsigned int VisitMatchBug::match_extract_field(const VisitMatchBug::State &s) {
  return s.value;
}

unsigned int VisitMatchBug::match_extract_two(const VisitMatchBug::State &s) {
  unsigned int v = s.value;
  unsigned int d = s.data;
  return (v + d);
}

unsigned int VisitMatchBug::match_nested(const VisitMatchBug::State &s) {
  return s.value;
}

unsigned int VisitMatchBug::match_in_tail(const VisitMatchBug::State &s) {
  return s.value;
}

unsigned int VisitMatchBug::match_in_expr(const VisitMatchBug::State &s) {
  return (s.value + 1u);
}
