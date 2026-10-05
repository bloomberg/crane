#ifndef INCLUDED_ITER_STEP_FUSION
#define INCLUDED_ITER_STEP_FUSION

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A, typename B> struct Sum;

template <typename A, typename B> struct Sum {
  // TYPES
  struct Inl {
    A a0;
  };

  struct Inr {
    B a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum() {}

  explicit Sum(Inl _v) : v_(std::move(_v)) {}

  explicit Sum(Inr _v) : v_(std::move(_v)) {}

  template <typename CraneU0, typename CraneU1>
  Sum(const Sum<CraneU0, CraneU1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sum<CraneU0, CraneU1>::Inl>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inl>(_other.v());
            return Inl{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU0 &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inr>(_other.v());
            return Inr{[&]() -> B {
              if constexpr (crane_convertible<B, const CraneU1 &>) {
                return crane_convert<B>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Sum<A, B> inl(A a0) { return Sum<A, B>(Inl{std::move(a0)}); }

  static Sum<A, B> inr(B a0) { return Sum<A, B>(Inr{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// An interaction-tree library in miniature, shaped as coq-itree's: iter
/// binds each step's result, and interp supplies the step as a literal
/// lambda.  Specializing iter to that lambda lets each passthrough step
/// build its next node directly instead of a Ret for bind to take
/// apart; interp_by_name, whose step is a definition, is the same
/// interpreter unspecialized.
struct IterStepFusion {
  template <typename R, typename itree> struct itreeF {
    // TYPES
    struct RetF {
      R r;
    };

    struct TauF {
      itree t;
    };

    struct VisF {
      uint64_t e;
      crane::fn<itree(uint64_t)> k;
    };

    using variant_t = std::variant<RetF, TauF, VisF>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    itreeF() {}

    explicit itreeF(RetF _v) : v_(std::move(_v)) {}

    explicit itreeF(TauF _v) : v_(std::move(_v)) {}

    explicit itreeF(VisF _v) : v_(std::move(_v)) {}

    template <typename CraneU0, typename CraneU1>
    itreeF(const itreeF<CraneU0, CraneU1> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename itreeF<CraneU0, CraneU1>::RetF>(
                    _other.v())) {
              const auto &[r] =
                  std::get<typename itreeF<CraneU0, CraneU1>::RetF>(_other.v());
              return RetF{[&]() -> R {
                if constexpr (crane_convertible<R, const CraneU0 &>) {
                  return crane_convert<R>(r);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              if (std::holds_alternative<
                      typename itreeF<CraneU0, CraneU1>::TauF>(_other.v())) {
                const auto &[t] =
                    std::get<typename itreeF<CraneU0, CraneU1>::TauF>(
                        _other.v());
                return TauF{[&]() -> itree {
                  if constexpr (crane_convertible<itree, const CraneU1 &>) {
                    return crane_convert<itree>(t);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }()};
              } else {
                const auto &[e, k] =
                    std::get<typename itreeF<CraneU0, CraneU1>::VisF>(
                        _other.v());
                return VisF{e, crane_convert<crane::fn<itree(uint64_t)>>(k)};
              }
            }
          }()) {}

    static itreeF<R, itree> retf(R r) {
      return itreeF<R, itree>(RetF{std::move(r)});
    }

    static itreeF<R, itree> tauf(itree t) {
      return itreeF<R, itree>(TauF{std::move(t)});
    }

    static itreeF<R, itree> visf(uint64_t e, crane::fn<itree(uint64_t)> k) {
      return itreeF<R, itree>(VisF{e, std::move(k)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename R> struct itree {
    // TYPES
    template <typename CraneS0 = itree<R>> struct Go_ {
      itreeF<R, CraneS0> _observe;
    };

    using Go = Go_<>;
    using variant_t = std::variant<Go>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    itree() {}

    explicit itree(Go _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    template <typename CraneU>
    itree(const itree<CraneU> &_other)
        : lazy_v_(crane::lazy<variant_t>::converted_from(
              _other.lazy_cell(), [=]() -> variant_t {
                const auto &[_observe] =
                    std::get<typename itree<CraneU>::Go>(_other.v());
                return Go{crane_convert<itreeF<R, itree<R>>>(_observe)};
              })) {}

    explicit itree(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static itree<R> go(itreeF<R, itree<R>> _observe) {
      return itree<R>(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<0>, std::move(_observe)));
    }

    explicit itree(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static itree<R> lazy_(F &&thunk) {
      return itree<R>(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  template <typename T1> static itreeF<T1, itree<T1>> observe_(itree<T1> i) {
    const auto &[_observe] = std::get<typename itree<T1>::Go>(i.v());
    return _observe;
  }

  template <typename T1> static itreeF<T1, itree<T1>> observe(itree<T1> x0_) {
    return observe_<T1>(x0_);
  }

  template <typename T1> static itree<T1> Ret(const T1 &r) {
    return itree<T1>::go(itreeF<T1, itree<T1>>::retf(r));
  }

  template <typename T1> static itree<T1> Tau(itree<T1> t) {
    return itree<T1>::go(itreeF<T1, itree<T1>>::tauf(t));
  }

  template <typename T1>
  static itree<T1> Vis(uint64_t e,
                       std::type_identity_t<crane::fn<itree<T1>(uint64_t)>> k) {
    return itree<T1>::go(itreeF<T1, itree<T1>>::visf(e, std::move(k)));
  }

  template <typename T1, typename T2>
  static itree<T2> subst(std::type_identity_t<crane::fn<itree<T2>(T1)>> k,
                         itree<T1> u) {
    auto &&_sv = observe<T1>(u);
    if (std::holds_alternative<typename itreeF<T1, itree<T1>>::RetF>(_sv.v())) {
      const auto &[r0] =
          std::get<typename itreeF<T1, itree<T1>>::RetF>(_sv.v());
      return itree<T2>::lazy_([=]() -> itree<T2> { return k(r0); });
    } else if (std::holds_alternative<typename itreeF<T1, itree<T1>>::TauF>(
                   _sv.v())) {
      const auto &[t0] =
          std::get<typename itreeF<T1, itree<T1>>::TauF>(_sv.v());
      return itree<T2>::lazy_(
          [=]() -> itree<T2> { return Tau<T2>(subst<T1, T2>(k, t0)); });
    } else {
      const auto &[e0, k0] =
          std::get<typename itreeF<T1, itree<T1>>::VisF>(_sv.v());
      return itree<T2>::lazy_([=]() -> itree<T2> {
        return Vis<T2>(e0, [=](uint64_t x) { return subst<T1, T2>(k, k0(x)); });
      });
    }
  }

  template <typename T1, typename T2>
  static itree<T2> bind(itree<T1> u,
                        std::type_identity_t<crane::fn<itree<T2>(T1)>> k) {
    return subst<T1, T2>(std::move(k), u);
  }

  template <typename T1, typename T2>
  static itree<T2>
  iter(std::type_identity_t<crane::fn<itree<Sum<T1, T2>>(T1)>> step0,
       const T1 &i) {
    return bind<Sum<T1, T2>, T2>(
        step0(i), [=](const Sum<T1, T2> &lr) -> itree<T2> {
          if (std::holds_alternative<typename Sum<T1, T2>::Inl>(lr.v())) {
            const auto &[a0] = std::get<typename Sum<T1, T2>::Inl>(lr.v());
            return Tau<T2>(iter<T1, T2>(step0, a0));
          } else {
            const auto &[a0] = std::get<typename Sum<T1, T2>::Inr>(lr.v());
            return Ret<T2>(a0);
          }
        });
  }

  template <typename T1, typename T2>
  static itree<T2> fmap(std::type_identity_t<crane::fn<T2(T1)>> f,
                        itree<T1> t) {
    return bind<T1, T2>(t, [=](const T1 &x) { return Ret<T2>(f(x)); });
  }

  /// Specialized: the step is a lambda.
  template <typename T1>
  static itree<T1> interp(crane::fn<itree<uint64_t>(uint64_t)> h, itree<T1> i) {
    auto &&_sv = observe<T1>(i);
    if (std::holds_alternative<typename itreeF<T1, itree<T1>>::RetF>(_sv.v())) {
      const auto &[r0] =
          std::get<typename itreeF<T1, itree<T1>>::RetF>(_sv.v());
      return itree<T1>::lazy_([=]() -> itree<T1> { return Ret<T1>(r0); });
    } else if (std::holds_alternative<typename itreeF<T1, itree<T1>>::TauF>(
                   _sv.v())) {
      const auto &[t0] =
          std::get<typename itreeF<T1, itree<T1>>::TauF>(_sv.v());
      return itree<T1>::lazy_(
          [=]() -> itree<T1> { return Tau<T1>(interp<T1>(h, t0)); });
    } else {
      const auto &[e0, k0] =
          std::get<typename itreeF<T1, itree<T1>>::VisF>(_sv.v());
      itree<Sum<itree<T1>, T1>> step0 = fmap<uint64_t, Sum<itree<T1>, T1>>(
          [=](uint64_t x) { return Sum<itree<T1>, T1>::inl(k0(x)); }, h(e0));
      return itree<T1>::lazy_([=]() -> itree<T1> {
        return bind<Sum<itree<T1>, T1>, T1>(
            step0, [=](const Sum<itree<T1>, T1> &lr) -> itree<T1> {
              if (std::holds_alternative<typename Sum<itree<T1>, T1>::Inl>(
                      lr.v())) {
                const auto &[a0] =
                    std::get<typename Sum<itree<T1>, T1>::Inl>(lr.v());
                return Tau<T1>(interp<T1>(h, a0));
              } else {
                const auto &[a0] =
                    std::get<typename Sum<itree<T1>, T1>::Inr>(lr.v());
                return Ret<T1>(a0);
              }
            });
      });
    }
  }

  /// Not specialized: the same step, by name.
  template <typename T1>
  static itree<Sum<itree<T1>, T1>> step(crane::fn<itree<uint64_t>(uint64_t)> h,
                                        itree<T1> t) {
    auto &&_sv = observe<T1>(t);
    if (std::holds_alternative<typename itreeF<T1, itree<T1>>::RetF>(_sv.v())) {
      const auto &[r0] =
          std::get<typename itreeF<T1, itree<T1>>::RetF>(_sv.v());
      return Ret<Sum<itree<T1>, T1>>(Sum<itree<T1>, T1>::inr(r0));
    } else if (std::holds_alternative<typename itreeF<T1, itree<T1>>::TauF>(
                   _sv.v())) {
      const auto &[t1] =
          std::get<typename itreeF<T1, itree<T1>>::TauF>(_sv.v());
      return Ret<Sum<itree<T1>, T1>>(Sum<itree<T1>, T1>::inl(t1));
    } else {
      const auto &[e0, k0] =
          std::get<typename itreeF<T1, itree<T1>>::VisF>(_sv.v());
      return fmap<uint64_t, Sum<itree<T1>, T1>>(
          [=](uint64_t x) { return Sum<itree<T1>, T1>::inl(k0(x)); }, h(e0));
    }
  }

  template <typename T1>
  static itree<T1> interp_by_name(crane::fn<itree<uint64_t>(uint64_t)> h,
                                  itree<T1> x0_) {
    return iter<itree<T1>, T1>(
        [=](itree<T1> _x0) -> itree<Sum<itree<T1>, T1>> {
          return step<T1>(h, _x0);
        },
        x0_);
  }
};

#endif // INCLUDED_ITER_STEP_FUSION
