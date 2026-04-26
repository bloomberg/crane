#ifndef INCLUDED_UNSOUND_AXIOMS
#define INCLUDED_UNSOUND_AXIOMS

#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

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
      return Rec{(*(this)).f1, (*(this)).f2};
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
      return ProofRec{(*(this)).pf_val, (*(this)).pf_val2};
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
