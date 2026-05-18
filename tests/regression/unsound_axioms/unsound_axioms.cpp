#include "unsound_axioms.h"

uint64_t UnsoundAxioms::cast_confusion(const UnsoundAxioms::Rec &r) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  return (unsafe_cast<uint64_t, uint64_t>(a) + b);
}

uint64_t UnsoundAxioms::choose_in_match(const UnsoundAxioms::Rec &r) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t witness = choose<uint64_t>();
  return ((a + b) + witness);
}

uint64_t
UnsoundAxioms::extract_proof_computation(const UnsoundAxioms::ProofRec &pr) {
  uint64_t v = pr.pf_val;
  uint64_t v2 = pr.pf_val2;
  return (v + v2);
}

bool UnsoundAxioms::use_type_eq(uint64_t n) { return n; }

UnsoundAxioms::Rec UnsoundAxioms::impossible_rec() {
  throw std::logic_error("unrealized axiom: "
                         "CraneTestsRegression.unsound_axioms.UnsoundAxioms."
                         "UnsoundAxioms.impossible_rec");
}

uint64_t UnsoundAxioms::use_impossible(std::monostate) {
  uint64_t a = impossible_rec().f1;
  uint64_t b = impossible_rec().f2;
  return (a + b);
}

uint64_t UnsoundAxioms::from_false(const UnsoundAxioms::Rec &) {
  throw std::logic_error("absurd case");
}

uint64_t UnsoundAxioms::prop_as_type() {
  throw std::logic_error("unrealized axiom: "
                         "CraneTestsRegression.unsound_axioms.UnsoundAxioms."
                         "UnsoundAxioms.prop_as_type");
}

uint64_t UnsoundAxioms::use_prop_as_type(const UnsoundAxioms::Rec &r) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  return ((prop_as_type() + a) + b);
}
