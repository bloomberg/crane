#ifndef INCLUDED_TUPLE
#define INCLUDED_TUPLE

#include <memory>
#include <utility>
#include <variant>

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A, typename B> struct Prod {
  // DATA
  A a0;
  B a1;

  // ACCESSORS
  Prod<A, B> clone() const { return {a0, a1}; }

  // CREATORS
  static Prod<A, B> pair(A a0, B a1) { return {std::move(a0), std::move(a1)}; }
};

struct Tuple {
  template <typename a, typename b> using pair = Prod<a, b>;

  template <typename T1, typename T2>
  static Prod<T1, T2> make_pair(T1 a, T2 b) {
    return Prod<T1, T2>::pair(a, b);
  }

  template <typename T1, typename T2> static T1 fst(Prod<T1, T2> p) {
    auto &[a0, a1] = p;
    return a0;
  }

  template <typename T1, typename T2> static T2 snd(Prod<T1, T2> p) {
    auto &[a0, a1] = p;
    return a1;
  }

  template <typename T1, typename T2> static Prod<T2, T1> swap(Prod<T1, T2> p) {
    auto &[a0, a1] = p;
    return Prod<T2, T1>::pair(std::move(a1), std::move(a0));
  }

  static inline const Prod<Nat, Nat> test_pair =
      make_pair<Nat, Nat>(Nat::s(Nat::o()), Nat::s(Nat::s(Nat::o())));
  static inline const Nat test_fst = fst<Nat, Nat>(test_pair);
  static inline const Prod<Nat, Nat> test_swap = swap<Nat, Nat>(test_pair);
};

#endif // INCLUDED_TUPLE
