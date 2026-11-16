#include "axiom_types.h"

AxiomTypes::MysteryType AxiomTypes::mystery_value() {
  throw std::logic_error(
      "unrealized axiom: "
      "CraneTestsRegression.axiom_types.AxiomTypes.AxiomTypes.mystery_value");
}

AxiomTypes::MysteryType AxiomTypes::mystery_function(AxiomTypes::MysteryType) {
  throw std::logic_error(
      "unrealized axiom: "
      "CraneTestsRegression.axiom_types.AxiomTypes.AxiomTypes.mystery_function");
}

AxiomTypes::MysteryType AxiomTypes::use_axiom() {
  return mystery_function(mystery_value());
}

AxiomTypes::AxiomRecord AxiomTypes::make_axiom_record() {
  return AxiomRecord{UINT64_C(42), mystery_value()};
}

AxiomTypes::MysteryType
AxiomTypes::extract_axiom_field(const AxiomTypes::AxiomRecord &r) {
  return r.axiom_field;
}

AxiomTypes::AxiomInductive AxiomTypes::use_axiom_inductive() {
  return AxiomInductive::axconstr2(mystery_value());
}

AxiomTypes::MysteryType AxiomTypes::axiom_identity(AxiomTypes::MysteryType x) {
  return x;
}

AxiomTypes::MysteryType AxiomTypes::nested_axiom() {
  return axiom_identity(mystery_function(axiom_identity(mystery_value())));
}

AxiomTypes::list<AxiomTypes::MysteryType> AxiomTypes::axiom_list() {
  return list<AxiomTypes::MysteryType>::cons(
      mystery_value(),
      list<AxiomTypes::MysteryType>::cons(mystery_function(mystery_value()),
                                          list<AxiomTypes::MysteryType>::nil()));
}

AxiomTypes::MysteryType AxiomTypes::use_poly_axiom() {
  return poly_axiom<AxiomTypes::MysteryType>(mystery_value());
}
