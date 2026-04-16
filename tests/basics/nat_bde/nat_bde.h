#ifndef INCLUDED_NAT_BDE
#define INCLUDED_NAT_BDE

#include <bdlf_overloaded.h>
#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_stdexcept.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_variant.h>

using namespace BloombergLP;
template <class From, class To>
concept convertible_to = bsl::is_convertible<From, To>::value;

template <class T, class U>
concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;

template <class F, class R, class... Args>
concept MapsTo = requires(F &f, Args &...a) {
  {
    bsl::invoke(static_cast<F &>(f), static_cast<Args &>(a)...)
  } -> convertible_to<R>;
};

struct Nat {
  // TYPES
  struct O {};
  struct S {
    bsl::shared_ptr<Nat> d_n;
  };
  using variant_t = bsl::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Nat(O _v) : d_v_(_v) {}
  explicit Nat(S _v) : d_v_(bsl::move(_v)) {}
  static bsl::shared_ptr<Nat> o() { return bsl::make_shared<Nat>(O{}); }
  static bsl::shared_ptr<Nat> s(const bsl::shared_ptr<Nat> &n) {
    return bsl::make_shared<Nat>(S{n});
  }
  static bsl::shared_ptr<Nat> s(bsl::shared_ptr<Nat> &&n) {
    return bsl::make_shared<Nat>(S{bsl::move(n)});
  }
  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }
  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
  template <typename T1, MapsTo<T1, bsl::shared_ptr<Nat>, T1> F1>
  T1 nat_rect(const T1 f, F1 &&f0) const {
    if (bsl::holds_alternative<typename Nat::O>(this->v())) {
      return f;
    } else {
      const auto &[d_n] = bsl::get<typename Nat::S>(this->v());
      return f0(d_n, d_n->template nat_rect<T1>(f, f0));
    }
  }
  template <typename T1, MapsTo<T1, bsl::shared_ptr<Nat>, T1> F1>
  T1 nat_rec(const T1 f, F1 &&f0) const {
    if (bsl::holds_alternative<typename Nat::O>(this->v())) {
      return f;
    } else {
      const auto &[d_n] = bsl::get<typename Nat::S>(this->v());
      return f0(d_n, d_n->template nat_rec<T1>(f, f0));
    }
  }
  bsl::shared_ptr<Nat> add(bsl::shared_ptr<Nat> n) const {
    if (bsl::holds_alternative<typename Nat::O>(this->v())) {
      return n;
    } else {
      const auto &[d_n] = bsl::get<typename Nat::S>(this->v());
      return Nat::s(d_n->add(n));
    }
  }
  __attribute__((pure)) int nat_to_int() const {
    if (bsl::holds_alternative<typename Nat::O>(this->v())) {
      return 0;
    } else {
      const auto &[d_n] = bsl::get<typename Nat::S>(this->v());
      return 1 + d_n->nat_to_int();
    }
  }
};

#endif // INCLUDED_NAT_BDE
