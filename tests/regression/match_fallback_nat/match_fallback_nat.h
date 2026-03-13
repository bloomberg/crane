#ifndef INCLUDED_MATCH_FALLBACK_NAT
#define INCLUDED_MATCH_FALLBACK_NAT

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

struct MatchFallbackNat {
  struct maybe_nat {
    // TYPES
    struct SomeNat {
      unsigned int d_a0;
    };

    struct NoneNat {};

    using variant_t = std::variant<SomeNat, NoneNat>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit maybe_nat(SomeNat _v) : d_v_(std::move(_v)) {}

    explicit maybe_nat(NoneNat _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<maybe_nat> SomeNat_(unsigned int a0) {
        return std::shared_ptr<maybe_nat>(new maybe_nat(SomeNat{a0}));
      }

      static std::shared_ptr<maybe_nat> NoneNat_() {
        return std::shared_ptr<maybe_nat>(new maybe_nat(NoneNat{}));
      }

      static std::unique_ptr<maybe_nat> SomeNat_uptr(unsigned int a0) {
        return std::unique_ptr<maybe_nat>(new maybe_nat(SomeNat{a0}));
      }

      static std::unique_ptr<maybe_nat> NoneNat_uptr() {
        return std::unique_ptr<maybe_nat>(new maybe_nat(NoneNat{}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 maybe_nat_rect(F0 &&f, const T1 f0,
                           const std::shared_ptr<maybe_nat> &m) {
    return std::visit(
        Overloaded{
            [&](const typename maybe_nat::SomeNat _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f(std::move(n));
            },
            [&](const typename maybe_nat::NoneNat _args) -> T1 { return f0; }},
        m->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 maybe_nat_rec(F0 &&f, const T1 f0,
                          const std::shared_ptr<maybe_nat> &m) {
    return std::visit(
        Overloaded{
            [&](const typename maybe_nat::SomeNat _args) -> T1 {
              unsigned int n = _args.d_a0;
              return f(std::move(n));
            },
            [&](const typename maybe_nat::NoneNat _args) -> T1 { return f0; }},
        m->v());
  }

  __attribute__((pure)) static unsigned int
  fallback(const std::shared_ptr<maybe_nat> &x);

  static inline const unsigned int t =
      (fallback(maybe_nat::ctor::NoneNat_()) +
       fallback(maybe_nat::ctor::SomeNat_(7u)));
};

#endif // INCLUDED_MATCH_FALLBACK_NAT
