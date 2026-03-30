#include <axiom_types.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

AxiomTypes::MysteryType AxiomTypes::mystery_value() {
  throw std::logic_error(
      "unrealized axiom: "
      "CraneTestsRegression.axiom_types.AxiomTypes.AxiomTypes.mystery_value");
}

AxiomTypes::MysteryType
AxiomTypes::mystery_function(const AxiomTypes::MysteryType _x0) {
  throw std::logic_error("unrealized axiom: "
                         "CraneTestsRegression.axiom_types.AxiomTypes."
                         "AxiomTypes.mystery_function");
}

AxiomTypes::MysteryType AxiomTypes::use_axiom(const std::monostate _x) {
  return mystery_function(mystery_value());
}

std::shared_ptr<AxiomTypes::AxiomRecord>
AxiomTypes::make_axiom_record(const std::monostate _x) {
  return std::make_shared<AxiomTypes::AxiomRecord>(
      AxiomRecord{42u, mystery_value()});
}

AxiomTypes::MysteryType AxiomTypes::extract_axiom_field(
    const std::shared_ptr<AxiomTypes::AxiomRecord> &r) {
  return r->axiom_field;
}

std::shared_ptr<AxiomTypes::AxiomInductive>
AxiomTypes::use_axiom_inductive(const std::monostate _x) {
  return AxiomInductive::axconstr2(mystery_value());
}

AxiomTypes::MysteryType
AxiomTypes::axiom_identity(const AxiomTypes::MysteryType x) {
  return x;
}

AxiomTypes::MysteryType AxiomTypes::nested_axiom(const std::monostate _x) {
  return axiom_identity(mystery_function(axiom_identity(mystery_value())));
}

std::shared_ptr<AxiomTypes::list<AxiomTypes::MysteryType>>
AxiomTypes::axiom_list(const std::monostate _x) {
  return list<AxiomTypes::MysteryType>::cons(
      mystery_value(), list<AxiomTypes::MysteryType>::cons(
                           mystery_function(mystery_value()),
                           list<AxiomTypes::MysteryType>::nil()));
}

AxiomTypes::MysteryType AxiomTypes::use_poly_axiom(const std::monostate _x) {
  return poly_axiom<AxiomTypes::MysteryType>(mystery_value());
}
