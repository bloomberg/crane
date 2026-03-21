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
    bsl::shared_ptr<Nat> d_a0;
  };
  using variant_t = bsl::variant<O, S>;

private:
  // DATA
  variant_t d_v_;
  // CREATORS
  explicit Nat(O _v) : d_v_(bsl::move(_v)) {}
  explicit Nat(S _v) : d_v_(bsl::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;
    static bsl::shared_ptr<Nat> O_() {
      return bsl::shared_ptr<Nat>(new Nat(O{}));
    }
    static bsl::shared_ptr<Nat> S_(const bsl::shared_ptr<Nat> &a0) {
      return bsl::shared_ptr<Nat>(new Nat(S{a0}));
    }
    static bsl::unique_ptr<Nat> O_uptr() {
      return bsl::unique_ptr<Nat>(new Nat(O{}));
    }
    static bsl::unique_ptr<Nat> S_uptr(const bsl::shared_ptr<Nat> &a0) {
      return bsl::unique_ptr<Nat>(new Nat(S{a0}));
    }
  };
  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }
  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
  __attribute__((pure)) int nat_to_int() const {
    return bsl::visit(
        bdlf::Overloaded{[](const typename Nat::O _args) -> int { return 0; },
                         [](const typename Nat::S _args) -> int {
                           return 1 + _args.d_a0->nat_to_int();
                         }},
        this->v());
  }
  template <typename T1, MapsTo<T1, bsl::shared_ptr<Nat>, T1> F1>
  T1 nat_rec(const T1 f, F1 &&f0) const {
    return bsl::visit(
        bdlf::Overloaded{[&](const typename Nat::O _args) -> T1 { return f; },
                         [&](const typename Nat::S _args) -> T1 {
                           return f0(_args.d_a0,
                                     _args.d_a0->template nat_rec<T1>(f, f0));
                         }},
        this->v());
  }
  template <typename T1, MapsTo<T1, bsl::shared_ptr<Nat>, T1> F1>
  T1 nat_rect(const T1 f, F1 &&f0) const {
    return bsl::visit(
        bdlf::Overloaded{[&](const typename Nat::O _args) -> T1 { return f; },
                         [&](const typename Nat::S _args) -> T1 {
                           return f0(_args.d_a0,
                                     _args.d_a0->template nat_rect<T1>(f, f0));
                         }},
        this->v());
  }
  bsl::shared_ptr<Nat> add(bsl::shared_ptr<Nat> n) const {
    return bsl::visit(
        bdlf::Overloaded{
            [&](const typename Nat::O _args) -> bsl::shared_ptr<Nat> {
              return n;
            },
            [&](const typename Nat::S _args) -> bsl::shared_ptr<Nat> {
              return Nat::ctor::S_(_args.d_a0->add(n));
            }},
        this->v());
  }
};

#endif // INCLUDED_NAT_BDE
