#ifndef INCLUDED_UNSOUND_AXIOMS
#define INCLUDED_UNSOUND_AXIOMS

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

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct UnsoundAxioms {
  template <typename T1, typename T2> static T2 unsafe_cast(const T1 _x0) {
    throw std::logic_error(
        "unrealized axiom: "
        "CraneTestsWIP.unsound_axioms.UnsoundAxioms.UnsoundAxioms.unsafe_cast");
  }

  static inline const std::any choose =
      ([]() -> const std::any { throw std::logic_error("unreachable"); })();

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
  static inline const unsigned int use_impossible = [](void) {
    unsigned int a = impossible_rec()->f1;
    unsigned int b = impossible_rec()->f2;
    return (a + std::move(b));
  }();
  __attribute__((pure)) static unsigned int
  from_false(const std::shared_ptr<Rec> &r);
  static inline const std::any prop_as_type =
      ([]() -> const std::any { throw std::logic_error("unreachable"); })();
  __attribute__((pure)) static unsigned int
  use_prop_as_type(const std::shared_ptr<Rec> &r);
};

#endif // INCLUDED_UNSOUND_AXIOMS
