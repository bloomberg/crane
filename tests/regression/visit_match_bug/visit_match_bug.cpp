#include "visit_match_bug.h"

VisitMatchBug::Tree VisitMatchBug::consume(VisitMatchBug::Tree t) { return t; }

uint64_t VisitMatchBug::match_after_consume(const VisitMatchBug::Tree &t) {
  VisitMatchBug::Tree t2 = consume(t);
  if (std::holds_alternative<typename VisitMatchBug::Tree::Leaf>(t2.v_mut())) {
    auto &[a0] = std::get<typename VisitMatchBug::Tree::Leaf>(t2.v_mut());
    return a0;
  } else {
    auto &[a0, a1, a2] =
        std::get<typename VisitMatchBug::Tree::Node>(t2.v_mut());
    return a1;
  }
}

uint64_t VisitMatchBug::match_last_use(const VisitMatchBug::Tree &t) {
  if (std::holds_alternative<typename VisitMatchBug::Tree::Leaf>(t.v())) {
    const auto &[a0] = std::get<typename VisitMatchBug::Tree::Leaf>(t.v());
    return a0;
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename VisitMatchBug::Tree::Node>(t.v());
    return a1;
  }
}

uint64_t VisitMatchBug::nested_match_consume(const VisitMatchBug::Tree &t) {
  VisitMatchBug::Tree t2 = consume(t);
  if (std::holds_alternative<typename VisitMatchBug::Tree::Leaf>(t2.v_mut())) {
    auto &[a0] = std::get<typename VisitMatchBug::Tree::Leaf>(t2.v_mut());
    return a0;
  } else {
    auto &[a0, a1, a2] =
        std::get<typename VisitMatchBug::Tree::Node>(t2.v_mut());
    return a1;
  }
}

uint64_t VisitMatchBug::chain_then_match(const VisitMatchBug::Tree &t1) {
  VisitMatchBug::Tree t2 = consume(t1);
  VisitMatchBug::Tree t3 = consume(std::move(t2));
  if (std::holds_alternative<typename VisitMatchBug::Tree::Leaf>(t3.v_mut())) {
    auto &[a0] = std::get<typename VisitMatchBug::Tree::Leaf>(t3.v_mut());
    return a0;
  } else {
    auto &[a0, a1, a2] =
        std::get<typename VisitMatchBug::Tree::Node>(t3.v_mut());
    return a1;
  }
}

uint64_t VisitMatchBug::match_extract_field(const VisitMatchBug::State &s) {
  return s.value;
}

uint64_t VisitMatchBug::match_extract_two(const VisitMatchBug::State &s) {
  uint64_t v = s.value;
  uint64_t d = s.data;
  return (v + d);
}

uint64_t VisitMatchBug::match_nested(const VisitMatchBug::State &s) {
  return s.value;
}

uint64_t VisitMatchBug::match_in_tail(const VisitMatchBug::State &s) {
  return s.value;
}

uint64_t VisitMatchBug::match_in_expr(const VisitMatchBug::State &s) {
  return (s.value + UINT64_C(1));
}
