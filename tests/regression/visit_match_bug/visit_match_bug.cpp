#include <visit_match_bug.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<VisitMatchBug::Tree>
VisitMatchBug::consume(std::shared_ptr<VisitMatchBug::Tree> t) {
  return t;
}

__attribute__((pure)) unsigned int VisitMatchBug::match_after_consume(
    const std::shared_ptr<VisitMatchBug::Tree> &t) {
  std::shared_ptr<VisitMatchBug::Tree> t2 = consume(t);
  return std::visit(
      Overloaded{
          [](const typename VisitMatchBug::Tree::Leaf _args) -> unsigned int {
            return _args.d_a0;
          },
          [](const typename VisitMatchBug::Tree::Node _args) -> unsigned int {
            return _args.d_a1;
          }},
      t2->v());
}

__attribute__((pure)) unsigned int
VisitMatchBug::match_last_use(const std::shared_ptr<VisitMatchBug::Tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename VisitMatchBug::Tree::Leaf _args) -> unsigned int {
            return _args.d_a0;
          },
          [](const typename VisitMatchBug::Tree::Node _args) -> unsigned int {
            return _args.d_a1;
          }},
      t->v());
}

__attribute__((pure)) unsigned int VisitMatchBug::nested_match_consume(
    const std::shared_ptr<VisitMatchBug::Tree> &t) {
  std::shared_ptr<VisitMatchBug::Tree> t2 = consume(t);
  return std::visit(
      Overloaded{
          [](const typename VisitMatchBug::Tree::Leaf _args) -> unsigned int {
            return _args.d_a0;
          },
          [](const typename VisitMatchBug::Tree::Node _args) -> unsigned int {
            return _args.d_a1;
          }},
      t2->v());
}

__attribute__((pure)) unsigned int VisitMatchBug::chain_then_match(
    const std::shared_ptr<VisitMatchBug::Tree> &t1) {
  std::shared_ptr<VisitMatchBug::Tree> t2 = consume(t1);
  std::shared_ptr<VisitMatchBug::Tree> t3 = consume(std::move(t2));
  return std::visit(
      Overloaded{
          [](const typename VisitMatchBug::Tree::Leaf _args) -> unsigned int {
            return _args.d_a0;
          },
          [](const typename VisitMatchBug::Tree::Node _args) -> unsigned int {
            return _args.d_a1;
          }},
      t3->v());
}

__attribute__((pure)) unsigned int VisitMatchBug::match_extract_field(
    const std::shared_ptr<VisitMatchBug::State> &s) {
  return s->value;
}

__attribute__((pure)) unsigned int VisitMatchBug::match_extract_two(
    const std::shared_ptr<VisitMatchBug::State> &s) {
  unsigned int v = s->value;
  unsigned int d = s->data;
  return (v + d);
}

__attribute__((pure)) unsigned int
VisitMatchBug::match_nested(const std::shared_ptr<VisitMatchBug::State> &s) {
  return s->value;
}

__attribute__((pure)) unsigned int
VisitMatchBug::match_in_tail(const std::shared_ptr<VisitMatchBug::State> &s) {
  return s->value;
}

__attribute__((pure)) unsigned int
VisitMatchBug::match_in_expr(const std::shared_ptr<VisitMatchBug::State> &s) {
  return (s->value + 1u);
}
