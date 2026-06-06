#ifndef INCLUDED_UNSOUND_AXIOMS
#define INCLUDED_UNSOUND_AXIOMS

#include <stdexcept>
#include <variant>

struct UnsoundAxioms {
  template <typename T1, typename T2> static T2 unsafe_cast(const T1 &) {
    throw std::logic_error("unrealized axiom: "
                           "CraneTestsRegression.unsound_axioms.UnsoundAxioms."
                           "UnsoundAxioms.unsafe_cast");
  }

  template <typename T1> static T1 choose() {
    throw std::logic_error("unrealized axiom: "
                           "CraneTestsRegression.unsound_axioms.UnsoundAxioms."
                           "UnsoundAxioms.choose");
  }

  struct Rec {
    uint64_t f1;
    uint64_t f2;
  };

  static uint64_t cast_confusion(const Rec &r);
  static uint64_t choose_in_match(const Rec &r);

  struct ProofRec {
    uint64_t pf_val;
    uint64_t pf_val2;
  };

  static uint64_t extract_proof_computation(const ProofRec &pr);
  static bool use_type_eq(uint64_t n);
  static Rec impossible_rec();
  static uint64_t use_impossible(std::monostate _x);
  static uint64_t from_false(const Rec &_x);
  static uint64_t prop_as_type();
  static uint64_t use_prop_as_type(const Rec &r);
};

#endif // INCLUDED_UNSOUND_AXIOMS
