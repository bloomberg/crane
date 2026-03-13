#include <unsound_axioms.h>

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

__attribute__((pure)) unsigned int
UnsoundAxioms::cast_confusion(const std::shared_ptr<UnsoundAxioms::Rec> &r) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    return (unsafe_cast<unsigned int, unsigned int>(a) + b);
  }();
}

__attribute__((pure)) unsigned int
UnsoundAxioms::choose_in_match(const std::shared_ptr<UnsoundAxioms::Rec> &r) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int witness = choose<unsigned int>();
    return ((a + b) + std::move(witness));
  }();
}

__attribute__((pure)) unsigned int UnsoundAxioms::extract_proof_computation(
    const std::shared_ptr<UnsoundAxioms::ProofRec> &pr) {
  return [&](void) {
    unsigned int v = pr->pf_val;
    unsigned int v2 = pr->pf_val2;
    return (v + v2);
  }();
}

__attribute__((pure)) bool UnsoundAxioms::use_type_eq(const unsigned int n) {
  return std::move(n);
}

std::shared_ptr<UnsoundAxioms::Rec> UnsoundAxioms::impossible_rec() {
  throw std::logic_error("unrealized axiom: "
                         "CraneTestsWIP.unsound_axioms.UnsoundAxioms."
                         "UnsoundAxioms.impossible_rec");
}

__attribute__((pure)) unsigned int
UnsoundAxioms::from_false(const std::shared_ptr<UnsoundAxioms::Rec> &r) {
  return [&](void) {
    std::any _x = r->f1;
    std::any _x0 = r->f2;
    throw std::logic_error("absurd case");
  }();
}

__attribute__((pure)) unsigned int
UnsoundAxioms::use_prop_as_type(const std::shared_ptr<UnsoundAxioms::Rec> &r) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    return ((prop_as_type() + a) + b);
  }();
}
