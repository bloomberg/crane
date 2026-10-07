#ifndef INCLUDED_MONAD_ALIAS_OF_APPLIED
#define INCLUDED_MONAD_ALIAS_OF_APPLIED

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename I>
concept Monad = requires {
  typename I::template m<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
  {
    I::template bind<crane::obj, crane::obj>(
        std::declval<typename I::template m<crane::obj>>(),
        std::declval<
            crane::fn<typename I::template m<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
};

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
  ~Nat() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool eqb(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return true;
        } else {
          return false;
        }
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return false;
        } else {
          const auto &[a00] = std::get<typename Nat::S>(_loop_m->v());
          _loop_self = crane_raw(a0);
          _loop_m = crane_raw(a00);
        }
      }
    }
  }
};

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
  template <Monad _tcI0, typename T2, typename T3, typename F1>
  static typename _tcI0::template m<T3> bind(typename _tcI0::template m<T2> x,
                                             F1 &&x0);
};

struct MonadAliasOfApplied {
  template <typename X> struct EOU {
    // TYPES
    struct Raise_error {
      Nat n;
    };

    struct Raise_ret {
      X x;
    };

    using variant_t = std::variant<Raise_error, Raise_ret>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    EOU() {}

    explicit EOU(Raise_error _v) : v_(std::move(_v)) {}

    explicit EOU(Raise_ret _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    EOU(const EOU<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename EOU<CraneU>::Raise_error>(
                    _other.v())) {
              const auto &[n] =
                  std::get<typename EOU<CraneU>::Raise_error>(_other.v());
              return Raise_error{n};
            } else {
              const auto &[x] =
                  std::get<typename EOU<CraneU>::Raise_ret>(_other.v());
              return Raise_ret{[&]() -> X {
                if constexpr (crane_convertible<X, const CraneU &>) {
                  return crane_convert<X>(x);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            }
          }()) {}

    static EOU<X> raise_error(Nat n) {
      return EOU<X>(Raise_error{std::move(n)});
    }

    static EOU<X> raise_ret(X x) { return EOU<X>(Raise_ret{std::move(x)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct EOU_monad {
    template <typename CraneA0> using m = EOU<CraneA0>;

    template <typename CraneA0> static EOU<CraneA0> ret(CraneA0 x) {
      return EOU<CraneA0>::raise_ret(std::move(x));
    }

    template <typename CraneA0, typename CraneA1>
    static EOU<CraneA1> bind(EOU<CraneA0> c,
                             crane::fn<EOU<CraneA1>(CraneA0)> k) {
      if (std::holds_alternative<typename EOU<CraneA0>::Raise_error>(c.v())) {
        const auto &[n] = std::get<typename EOU<CraneA0>::Raise_error>(c.v());
        return EOU<CraneA1>::raise_error(n);
      } else {
        const auto &[x0] = std::get<typename EOU<CraneA0>::Raise_ret>(c.v());
        return k(x0);
      }
    }
  };

  static_assert(Monad<EOU_monad>);

  template <typename A> struct MaybePoison {
    // TYPES
    struct Pois {};

    struct NoPois {
      A a;
    };

    using variant_t = std::variant<Pois, NoPois>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    MaybePoison() {}

    explicit MaybePoison(Pois _v) : v_(_v) {}

    explicit MaybePoison(NoPois _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    MaybePoison(const MaybePoison<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename MaybePoison<CraneU>::Pois>(
                    _other.v())) {
              return Pois{};
            } else {
              const auto &[a] =
                  std::get<typename MaybePoison<CraneU>::NoPois>(_other.v());
              return NoPois{[&]() -> A {
                if constexpr (crane_convertible<A, const CraneU &>) {
                  return crane_convert<A>(a);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            }
          }()) {}

    static MaybePoison<A> pois() { return MaybePoison<A>(Pois{}); }

    static MaybePoison<A> nopois(A a) {
      return MaybePoison<A>(NoPois{std::move(a)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename z> using EOUP = EOU<MaybePoison<z>>;

  struct EOUP_Monad {
    template <typename CraneA0> using m = EOU<MaybePoison<CraneA0>>;

    template <typename CraneA0>
    static EOU<MaybePoison<CraneA0>> ret(CraneA0 a) {
      return EOU_monad::template ret<MaybePoison<CraneA0>>(
          MaybePoison<CraneA0>::nopois(std::move(a)));
    }

    template <typename CraneA0, typename CraneA1>
    static EOU<MaybePoison<CraneA1>>
    bind(EOU<MaybePoison<CraneA0>> c,
         crane::fn<EOU<MaybePoison<CraneA1>>(CraneA0)> k) {
      return EOU_monad::template bind<MaybePoison<CraneA0>,
                                      MaybePoison<CraneA1>>(
          std::move(c),
          [=, k = std::move(k)](
              const MaybePoison<CraneA0> &pov) -> EOU<MaybePoison<CraneA1>> {
            if (std::holds_alternative<typename MaybePoison<CraneA0>::Pois>(
                    pov.v())) {
              return EOU_monad::template ret<MaybePoison<CraneA1>>(
                  MaybePoison<CraneA1>::pois());
            } else {
              const auto &[a0] =
                  std::get<typename MaybePoison<CraneA0>::NoPois>(pov.v());
              return k(a0);
            }
          });
    }
  };

  static_assert(Monad<EOUP_Monad>);
  static EOUP<Nat> extract(bool b, const Nat &n);
  static inline const bool is_three = []() {
    auto &&_sv = extract(true, Nat::s(Nat::s(Nat::o())));
    if (std::holds_alternative<typename EOU<MaybePoison<Nat>>::Raise_error>(
            _sv.v())) {
      return false;
    } else {
      const auto &[x0] =
          std::get<typename EOU<MaybePoison<Nat>>::Raise_ret>(_sv.v());
      if (std::holds_alternative<typename MaybePoison<Nat>::Pois>(x0.v())) {
        return false;
      } else {
        const auto &[a0] = std::get<typename MaybePoison<Nat>::NoPois>(x0.v());
        return a0.eqb(Nat::s(Nat::s(Nat::s(Nat::o()))));
      }
    }
  }();
};

template <Monad _tcI0, typename T2>
typename _tcI0::template m<T2> Monad0::ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

template <Monad _tcI0, typename T2, typename T3, typename F1>
typename _tcI0::template m<T3> Monad0::bind(typename _tcI0::template m<T2> x,
                                            F1 &&x0) {
  return _tcI0::template bind<T2, T3>(std::move(x), x0);
}

#endif // INCLUDED_MONAD_ALIAS_OF_APPLIED
