#include <axiom_types.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) AxiomTypes::MysteryType AxiomTypes::mystery_value() {
  throw std::logic_error(
      "unrealized axiom: "
      "CraneTestsRegression.axiom_types.AxiomTypes.AxiomTypes.mystery_value");
}

__attribute__((pure)) AxiomTypes::MysteryType
AxiomTypes::mystery_function(const AxiomTypes::MysteryType _x0) {
  throw std::logic_error("unrealized axiom: "
                         "CraneTestsRegression.axiom_types.AxiomTypes."
                         "AxiomTypes.mystery_function");
}

__attribute__((pure)) AxiomTypes::MysteryType
AxiomTypes::use_axiom(const Unit _x) {
  return mystery_function(mystery_value());
}

std::shared_ptr<AxiomTypes::AxiomRecord>
AxiomTypes::make_axiom_record(const Unit _x) {
  return std::make_shared<AxiomTypes::AxiomRecord>(
      AxiomRecord{42u, mystery_value()});
}

__attribute__((pure)) AxiomTypes::MysteryType AxiomTypes::extract_axiom_field(
    const std::shared_ptr<AxiomTypes::AxiomRecord> &r) {
  return r->axiom_field;
}

std::shared_ptr<AxiomTypes::AxiomInductive>
AxiomTypes::use_axiom_inductive(const Unit _x) {
  return AxiomInductive::ctor::AxConstr2_(mystery_value());
}

__attribute__((pure)) AxiomTypes::MysteryType
AxiomTypes::axiom_identity(const AxiomTypes::MysteryType x) {
  return x;
}

__attribute__((pure)) AxiomTypes::MysteryType
AxiomTypes::nested_axiom(const Unit _x) {
  return axiom_identity(mystery_function(axiom_identity(mystery_value())));
}

std::shared_ptr<AxiomTypes::list<AxiomTypes::MysteryType>>
AxiomTypes::axiom_list(const Unit _x) {
  return list<AxiomTypes::MysteryType>::ctor::Cons_(
      mystery_value(), list<AxiomTypes::MysteryType>::ctor::Cons_(
                           mystery_function(mystery_value()),
                           list<AxiomTypes::MysteryType>::ctor::Nil_()));
}

__attribute__((pure)) AxiomTypes::MysteryType
AxiomTypes::use_poly_axiom(const Unit _x) {
  return poly_axiom<AxiomTypes::MysteryType>(mystery_value());
}
