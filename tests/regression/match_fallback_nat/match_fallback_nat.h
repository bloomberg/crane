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
  public:
    struct SomeNat {
      unsigned int _a0;
    };
    struct NoneNat {};
    using variant_t = std::variant<SomeNat, NoneNat>;

  private:
    variant_t v_;
    explicit maybe_nat(SomeNat _v) : v_(std::move(_v)) {}
    explicit maybe_nat(NoneNat _v) : v_(std::move(_v)) {}

  public:
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
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0>
  static T1 maybe_nat_rect(F0 &&f, const T1 f0,
                           const std::shared_ptr<maybe_nat> &m) {
    return std::visit(
        Overloaded{
            [&](const typename maybe_nat::SomeNat _args) -> T1 {
              unsigned int n = _args._a0;
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
              unsigned int n = _args._a0;
              return f(std::move(n));
            },
            [&](const typename maybe_nat::NoneNat _args) -> T1 { return f0; }},
        m->v());
  }

  static unsigned int fallback(const std::shared_ptr<maybe_nat> &x);

  static inline const unsigned int t =
      (fallback(maybe_nat::ctor::NoneNat_()) +
       fallback(maybe_nat::ctor::SomeNat_(
           (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1))));
};
