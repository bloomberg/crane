#ifndef INCLUDED_UNSOUND_AXIOMS
#define INCLUDED_UNSOUND_AXIOMS

#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct UnsoundAxioms {
  template <typename T1, typename T2> static T2 unsafe_cast(const T1) {
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
    unsigned int f1;
    unsigned int f2;

    // ACCESSORS
    Rec clone() const { return Rec{(*(this)).f1, (*(this)).f2}; }
  };

  static unsigned int cast_confusion(const Rec &r);
  static unsigned int choose_in_match(const Rec &r);

  struct ProofRec {
    unsigned int pf_val;
    unsigned int pf_val2;

    // ACCESSORS
    ProofRec clone() const {
      return ProofRec{(*(this)).pf_val, (*(this)).pf_val2};
    }
  };

  static unsigned int extract_proof_computation(const ProofRec &pr);
  static bool use_type_eq(unsigned int n);
  static Rec impossible_rec();
  static unsigned int use_impossible(const std::monostate &_x);
  static unsigned int from_false(const Rec &_x);
  static unsigned int prop_as_type();
  static unsigned int use_prop_as_type(const Rec &r);
};

#endif // INCLUDED_UNSOUND_AXIOMS
