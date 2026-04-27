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

    __attribute__((pure)) Rec *operator->() { return this; }

    __attribute__((pure)) const Rec *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) Rec clone() const {
      return Rec{[](auto &&__v) -> unsigned int {
                   if constexpr (
                       requires { __v ? 0 : 0; } && requires { *__v; } &&
                       requires { __v->clone(); } && requires { __v.get(); }) {
                     using _E = std::remove_cvref_t<decltype(*__v)>;
                     return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
                   } else if constexpr (requires { __v.clone(); }) {
                     return __v.clone();
                   } else {
                     return __v;
                   }
                 }((*this).f1),
                 [](auto &&__v) -> unsigned int {
                   if constexpr (
                       requires { __v ? 0 : 0; } && requires { *__v; } &&
                       requires { __v->clone(); } && requires { __v.get(); }) {
                     using _E = std::remove_cvref_t<decltype(*__v)>;
                     return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
                   } else if constexpr (requires { __v.clone(); }) {
                     return __v.clone();
                   } else {
                     return __v;
                   }
                 }((*this).f2)};
    }
  };

  __attribute__((pure)) static unsigned int cast_confusion(const Rec &r);
  __attribute__((pure)) static unsigned int choose_in_match(const Rec &r);

  struct ProofRec {
    unsigned int pf_val;
    unsigned int pf_val2;

    __attribute__((pure)) ProofRec *operator->() { return this; }

    __attribute__((pure)) const ProofRec *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) ProofRec clone() const {
      return ProofRec{
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).pf_val),
          [](auto &&__v) -> unsigned int {
            if constexpr (
                requires { __v ? 0 : 0; } && requires { *__v; } &&
                requires { __v->clone(); } && requires { __v.get(); }) {
              using _E = std::remove_cvref_t<decltype(*__v)>;
              return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
            } else if constexpr (requires { __v.clone(); }) {
              return __v.clone();
            } else {
              return __v;
            }
          }((*this).pf_val2)};
    }
  };

  __attribute__((pure)) static unsigned int
  extract_proof_computation(const ProofRec &pr);
  __attribute__((pure)) static bool use_type_eq(unsigned int n);
  static Rec impossible_rec();
  static unsigned int use_impossible(const std::monostate &_x);
  static unsigned int from_false(const Rec &_x);
  static unsigned int prop_as_type();
  __attribute__((pure)) static unsigned int use_prop_as_type(const Rec &r);
};

#endif // INCLUDED_UNSOUND_AXIOMS
