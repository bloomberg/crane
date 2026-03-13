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
  struct nat {
    // TYPES
    struct O {};
    struct S {
      bsl::shared_ptr<nat> d_a0;
    };
    using variant_t = bsl::variant<O, S>;

  private:
    // DATA
    variant_t d_v_;
    // CREATORS
    explicit nat(O _v) : d_v_(bsl::move(_v)) {}
    explicit nat(S _v) : d_v_(bsl::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;
      static bsl::shared_ptr<nat> O_() {
        return bsl::shared_ptr<nat>(new nat(O{}));
      }
      static bsl::shared_ptr<nat> S_(const bsl::shared_ptr<nat> &a0) {
        return bsl::shared_ptr<nat>(new nat(S{a0}));
      }
      static bsl::unique_ptr<nat> O_uptr() {
        return bsl::unique_ptr<nat>(new nat(O{}));
      }
      static bsl::unique_ptr<nat> S_uptr(const bsl::shared_ptr<nat> &a0) {
        return bsl::unique_ptr<nat>(new nat(S{a0}));
      }
    };
    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }
    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
    __attribute__((pure)) int nat_to_int() const {
      return bsl::visit(
          bdlf::Overloaded{[](const typename nat::O _args) -> int { return 0; },
                           [](const typename nat::S _args) -> int {
                             bsl::shared_ptr<nat> n_ = _args.d_a0;
                             return 1 + bsl::move(n_)->nat_to_int();
                           }},
          this->v());
    }
    template <typename T1, MapsTo<T1, bsl::shared_ptr<nat>, T1> F1>
    T1 nat_rec(const T1 f, F1 &&f0) const {
      return bsl::visit(
          bdlf::Overloaded{[&](const typename nat::O _args) -> T1 { return f; },
                           [&](const typename nat::S _args) -> T1 {
                             bsl::shared_ptr<nat> n0 = _args.d_a0;
                             return f0(n0, n0->template nat_rec<T1>(f, f0));
                           }},
          this->v());
    }
    template <typename T1, MapsTo<T1, bsl::shared_ptr<nat>, T1> F1>
    T1 nat_rect(const T1 f, F1 &&f0) const {
      return bsl::visit(
          bdlf::Overloaded{[&](const typename nat::O _args) -> T1 { return f; },
                           [&](const typename nat::S _args) -> T1 {
                             bsl::shared_ptr<nat> n0 = _args.d_a0;
                             return f0(n0, n0->template nat_rect<T1>(f, f0));
                           }},
          this->v());
    }
    bsl::shared_ptr<nat> add(bsl::shared_ptr<nat> n) const {
      return bsl::visit(
          bdlf::Overloaded{
              [&](const typename nat::O _args) -> bsl::shared_ptr<nat> {
                return n;
              },
              [&](const typename nat::S _args) -> bsl::shared_ptr<nat> {
                bsl::shared_ptr<nat> x = _args.d_a0;
                return nat::ctor::S_(bsl::move(x)->add(n));
              }},
          this->v());
    }
  };
};

#endif // INCLUDED_NAT_BDE
