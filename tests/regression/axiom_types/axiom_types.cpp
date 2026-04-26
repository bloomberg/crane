#include <axiom_types.h>

#include <any>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

AxiomTypes::MysteryType AxiomTypes::mystery_value() {
  throw std::logic_error(
      "unrealized axiom: "
      "CraneTestsRegression.axiom_types.AxiomTypes.AxiomTypes.mystery_value");
}

AxiomTypes::MysteryType
AxiomTypes::mystery_function(const AxiomTypes::MysteryType) {
  throw std::logic_error("unrealized axiom: "
                         "CraneTestsRegression.axiom_types.AxiomTypes."
                         "AxiomTypes.mystery_function");
}

AxiomTypes::MysteryType AxiomTypes::use_axiom(const std::monostate &) {
  return mystery_function(mystery_value());
}

AxiomTypes::AxiomRecord AxiomTypes::make_axiom_record(const std::monostate &) {
  return AxiomRecord{42u, mystery_value()};
}

AxiomTypes::MysteryType
AxiomTypes::extract_axiom_field(const AxiomTypes::AxiomRecord &r) {
  return r.axiom_field;
}

AxiomTypes::AxiomInductive
AxiomTypes::use_axiom_inductive(const std::monostate &) {
  return AxiomInductive::axconstr2(mystery_value());
}

AxiomTypes::MysteryType
AxiomTypes::axiom_identity(const AxiomTypes::MysteryType x) {
  return x;
}

AxiomTypes::MysteryType AxiomTypes::nested_axiom(const std::monostate &) {
  return axiom_identity(mystery_function(axiom_identity(mystery_value())));
}

AxiomTypes::list<AxiomTypes::MysteryType>
AxiomTypes::axiom_list(const std::monostate &) {
  return list<AxiomTypes::MysteryType>::cons(
      mystery_value(), list<AxiomTypes::MysteryType>::cons(
                           mystery_function(mystery_value()),
                           list<AxiomTypes::MysteryType>::nil()));
}

AxiomTypes::MysteryType AxiomTypes::use_poly_axiom(const std::monostate &) {
  return poly_axiom<AxiomTypes::MysteryType>(mystery_value());
}
