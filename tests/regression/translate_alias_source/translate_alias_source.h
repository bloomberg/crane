#ifndef INCLUDED_TRANSLATE_ALIAS_SOURCE
#define INCLUDED_TRANSLATE_ALIAS_SOURCE

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename E, typename R, typename itree> struct ItreeF;
template <typename E, typename R> struct Itree;
template <typename E1, typename E2, typename X> struct Sum1;

template <typename E, typename R, typename itree> struct ItreeF {
  // TYPES
  struct RetF {
    R r;
  };

  struct TauF {
    itree t;
  };

  struct VisF {
    E x;
    crane::fn<itree(crane::obj)> e;
  };

  using variant_t = std::variant<RetF, TauF, VisF>;
  using crane_family_tag = void;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  ItreeF() {}

  explicit ItreeF(RetF _v) : v_(std::move(_v)) {}

  explicit ItreeF(TauF _v) : v_(std::move(_v)) {}

  explicit ItreeF(VisF _v) : v_(std::move(_v)) {}

  template <typename CraneU0, typename CraneU1, typename CraneU2>
  ItreeF(const ItreeF<CraneU0, CraneU1, CraneU2> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<
                  typename ItreeF<CraneU0, CraneU1, CraneU2>::RetF>(
                  _other.v())) {
            const auto &[r] =
                std::get<typename ItreeF<CraneU0, CraneU1, CraneU2>::RetF>(
                    _other.v());
            return RetF{[&]() -> R {
              if constexpr (crane_convertible<R, const CraneU1 &>) {
                return crane_convert<R>(r);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            if (std::holds_alternative<
                    typename ItreeF<CraneU0, CraneU1, CraneU2>::TauF>(
                    _other.v())) {
              const auto &[t] =
                  std::get<typename ItreeF<CraneU0, CraneU1, CraneU2>::TauF>(
                      _other.v());
              return TauF{[&]() -> itree {
                if constexpr (crane_convertible<itree, const CraneU2 &>) {
                  return crane_convert<itree>(t);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              const auto &[x, e] =
                  std::get<typename ItreeF<CraneU0, CraneU1, CraneU2>::VisF>(
                      _other.v());
              return VisF{
                  [&]() -> E {
                    if constexpr (crane_convertible<E, const CraneU0 &>) {
                      return crane_convert<E>(x);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  crane_convert<crane::fn<itree(crane::obj)>>(e)};
            }
          }
        }()) {}

  static ItreeF<E, R, itree> retf(R r) {
    return ItreeF<E, R, itree>(RetF{std::move(r)});
  }

  static ItreeF<E, R, itree> tauf(itree t) {
    return ItreeF<E, R, itree>(TauF{std::move(t)});
  }

  static ItreeF<E, R, itree> visf(E x, crane::fn<itree(crane::obj)> e) {
    return ItreeF<E, R, itree>(VisF{std::move(x), std::move(e)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename E, typename R> struct Itree {
  // TYPES
  template <typename CraneS0 = Itree<E, R>> struct Go_ {
    ItreeF<E, R, CraneS0> _observe;
  };

  using Go = Go_<>;
  using variant_t = std::variant<Go>;
  using crane_family_tag = void;

private:
  // DATA
  crane::lazy<variant_t> lazy_v_;

public:
  // CREATORS
  Itree() {}

  explicit Itree(Go _v)
      : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  template <typename CraneU0, typename CraneU1>
  Itree(const Itree<CraneU0, CraneU1> &_other)
      : lazy_v_(crane::lazy<variant_t>::converted_from(
            _other.lazy_cell(), [=]() -> variant_t {
              const auto &[_observe] =
                  std::get<typename Itree<CraneU0, CraneU1>::Go>(_other.v());
              return Go{crane_convert<ItreeF<E, R, Itree<E, R>>>(_observe)};
            })) {}

  explicit Itree(crane::fn<variant_t()> _thunk)
      : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  static Itree<E, R> go(ItreeF<E, R, Itree<E, R>> _observe) {
    return Itree<E, R>(crane::lazy<variant_t>(
        std::in_place, std::in_place_index<0>, std::move(_observe)));
  }

  explicit Itree(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

  template <typename F> static Itree<E, R> lazy_(F &&thunk) {
    return Itree<E, R>(
        crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
  }

  // ACCESSORS
  const variant_t &v() const { return lazy_v_.force(); }

  const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }

  const ItreeF<E, R, Itree<E, R>> &observe() const & {
    const auto &[_observe] = std::get<typename Itree<E, R>::Go>(this->v());
    return _observe;
  }

  ItreeF<E, R, Itree<E, R>> observe() const && {
    const auto &[_observe] = std::get<typename Itree<E, R>::Go>(this->v());
    return _observe;
  }
};

template <typename E1, typename E2, typename X> struct Sum1 {
  // TYPES
  struct Inl1 {
    crane::rebind_t<E1, X> a0;
  };

  struct Inr1 {
    crane::rebind_t<E2, X> a0;
  };

  using variant_t = std::variant<Inl1, Inr1>;
  using crane_family_tag = void;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum1() {}

  explicit Sum1(Inl1 _v) : v_(std::move(_v)) {}

  explicit Sum1(Inr1 _v) : v_(std::move(_v)) {}

  template <typename CraneU0, typename CraneU1, typename CraneU2>
  Sum1(const Sum1<CraneU0, CraneU1, CraneU2> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<
                  typename Sum1<CraneU0, CraneU1, CraneU2>::Inl1>(_other.v())) {
            const auto &[a0] =
                std::get<typename Sum1<CraneU0, CraneU1, CraneU2>::Inl1>(
                    _other.v());
            return Inl1{[&]() -> E1 {
              if constexpr (crane_convertible<E1, const CraneU0 &>) {
                return crane_convert<E1>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum1<CraneU0, CraneU1, CraneU2>::Inr1>(
                    _other.v());
            return Inr1{[&]() -> E2 {
              if constexpr (crane_convertible<E2, const CraneU1 &>) {
                return crane_convert<E2>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Sum1<E1, E2, X> inl1(crane::rebind_t<E1, X> a0) {
    return Sum1<E1, E2, X>(Inl1{std::move(a0)});
  }

  static Sum1<E1, E2, X> inr1(crane::rebind_t<E2, X> a0) {
    return Sum1<E1, E2, X>(Inr1{std::move(a0)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Interp {
  template <typename T1, typename T2, typename T3>
  static Itree<T2, T3>
  translateF(const std::type_identity_t<crane::fn<T2(T1)>> &h,
             std::type_identity_t<crane::fn<Itree<T2, T3>(Itree<T1, T3>)>> rec,
             const ItreeF<T1, T3, Itree<T1, T3>> &t);
  template <typename T1, typename T2, typename T3>
  static Itree<T2, T3>
  translate(const std::type_identity_t<crane::fn<T2(T1)>> &h,
            const Itree<T1, T3> &t);
};

struct TranslateAliasSource {
  enum class AE { A };
  enum class BE { B };
  enum class CE { C };
  template <typename x> using SrcE = Sum1<AE, BE, x>;
  template <typename x> using DstE = Sum1<CE, SrcE<crane::obj>, x>;
  template <typename r> using SrcTop = Itree<SrcE<crane::obj>, r>;
  template <typename r> using DstTop = Itree<DstE<crane::obj>, r>;

  template <typename T1>
  static DstTop<T1> lift(const Itree<Sum1<AE, BE, crane::obj>, T1> &x) {
    return Interp::template translate<Sum1<AE, BE, crane::obj>,
                                      DstE<crane::obj>, T1>(
        [](crane::obj x0) {
          return Sum1<crane::obj, crane::obj, crane::obj>::inr1(x0);
        },
        x);
  }

  static inline const SrcTop<uint64_t> prog = []() {
    return Itree<Sum1<AE, BE, crane::obj>, uint64_t>::go(
        ItreeF<Sum1<AE, BE, crane::obj>, uint64_t,
               Itree<Sum1<AE, BE, crane::obj>, uint64_t>>::
            tauf(Itree<Sum1<AE, BE, crane::obj>, uint64_t>::go(
                ItreeF<Sum1<AE, BE, crane::obj>, uint64_t,
                       Itree<Sum1<AE, BE, crane::obj>, uint64_t>>::
                    visf(
                        Sum1<AE, BE, AE>::inl1(AE::A),
                        crane::fn<Itree<Sum1<AE, BE, crane::obj>, uint64_t>(
                            crane::obj)>([](const crane::obj &x)
                                             -> Itree<Sum1<AE, BE, crane::obj>,
                                                      uint64_t> {
                          return Itree<Sum1<AE, BE, crane::obj>, uint64_t>::
                              lazy_([=]() -> typename Itree<
                                              Sum1<AE, BE, crane::obj>,
                                              uint64_t>::Go {
                                return {ItreeF<
                                    Sum1<AE, BE, crane::obj>, uint64_t,
                                    Itree<Sum1<AE, BE, crane::obj>, uint64_t>>::
                                            retf((crane::any_cast<uint64_t>(x) +
                                                  UINT64_C(1)))};
                              });
                        })))));
  }();
  static uint64_t
  run(uint64_t fuel,
      const Itree<Sum1<CE, Sum1<AE, BE, crane::obj>, crane::obj>, uint64_t> &t);
  static inline const uint64_t result = run(UINT64_C(10), lift<uint64_t>(prog));
};

template <typename T1, typename T2, typename T3>
Itree<T2, T3> Interp::translateF(
    const std::type_identity_t<crane::fn<T2(T1)>> &h,
    std::type_identity_t<crane::fn<Itree<T2, T3>(Itree<T1, T3>)>> rec,
    const ItreeF<T1, T3, Itree<T1, T3>> &t) {
  if (std::holds_alternative<typename ItreeF<T1, T3, Itree<T1, T3>>::RetF>(
          t.v())) {
    const auto &[r] =
        std::get<typename ItreeF<T1, T3, Itree<T1, T3>>::RetF>(t.v());
    return Itree<T2, T3>::go(ItreeF<T2, T3, Itree<T2, T3>>::retf(r));
  } else if (std::holds_alternative<
                 typename ItreeF<T1, T3, Itree<T1, T3>>::TauF>(t.v())) {
    const auto &[t1] =
        std::get<typename ItreeF<T1, T3, Itree<T1, T3>>::TauF>(t.v());
    return Itree<T2, T3>::lazy_(
        [=, rec = std::move(rec)]() -> typename Itree<T2, T3>::Go {
          return {ItreeF<T2, T3, Itree<T2, T3>>::tauf(rec(t1))};
        });
  } else {
    const auto &[x, e0] =
        std::get<typename ItreeF<T1, T3, Itree<T1, T3>>::VisF>(t.v());
    return Itree<T2, T3>::lazy_(
        [=, rec = std::move(rec)]() -> typename Itree<T2, T3>::Go {
          return {ItreeF<T2, T3, Itree<T2, T3>>::visf(
              h(x), crane::fn<Itree<T2, T3>(crane::obj)>(
                        [=](const crane::obj &x0) -> Itree<T2, T3> {
                          return rec(crane_call_erased(e0, x0));
                        }))};
        });
  }
}

template <typename T1, typename T2, typename T3>
Itree<T2, T3>
Interp::translate(const std::type_identity_t<crane::fn<T2(T1)>> &h,
                  const Itree<T1, T3> &t) {
  return Itree<T2, T3>::lazy_([=]() -> Itree<T2, T3> {
    return Interp::template translateF<T1, T2, T3>(
        h,
        [=](Itree<T1, T3> _x0) -> Itree<T2, T3> {
          return Interp::template translate<T1, T2, T3>(h, _x0);
        },
        t.observe());
  });
}

#endif // INCLUDED_TRANSLATE_ALIAS_SOURCE
