#ifndef INCLUDED_UNSOUND_AXIOMS
#define INCLUDED_UNSOUND_AXIOMS

#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct UnsoundAxioms {
  template <typename T1, typename T2> static T2 unsafe_cast(const T1 _x0) {
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
  };

  __attribute__((pure)) static unsigned int
  cast_confusion(const std::shared_ptr<Rec> &r);
  __attribute__((pure)) static unsigned int
  choose_in_match(const std::shared_ptr<Rec> &r);

  struct ProofRec {
    unsigned int pf_val;
    unsigned int pf_val2;
  };

  __attribute__((pure)) static unsigned int
  extract_proof_computation(const std::shared_ptr<ProofRec> &pr);
  __attribute__((pure)) static bool use_type_eq(const unsigned int n);
  static std::shared_ptr<Rec> impossible_rec();
  __attribute__((pure)) static unsigned int
  use_impossible(const std::monostate _x);
  __attribute__((pure)) static unsigned int
  from_false(const std::shared_ptr<Rec> &_x);
  static unsigned int prop_as_type();
  __attribute__((pure)) static unsigned int
  use_prop_as_type(const std::shared_ptr<Rec> &r);
};

#endif // INCLUDED_UNSOUND_AXIOMS
