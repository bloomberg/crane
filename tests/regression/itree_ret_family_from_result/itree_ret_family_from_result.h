#ifndef INCLUDED_ITREE_RET_FAMILY_FROM_RESULT
#define INCLUDED_ITREE_RET_FAMILY_FROM_RESULT

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A, typename B> struct Sum;
template <typename E, typename R, typename itree> struct ItreeF;
template <typename E, typename R> struct Itree;
template <typename E1, typename E2, typename X> struct Sum1;

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

struct ItreeRetFamilyFromResult {
  enum class AE { A };

  struct BE {
    // DATA
    uint64_t a0;

    // ACCESSORS
    BE clone() const { return {a0}; }

    // CREATORS
    static BE b(uint64_t a0) { return {a0}; }
  };

  template <typename x> using TopE = Sum1<AE, BE, x>;
  template <typename r> using top = Itree<TopE<crane::obj>, r>;

  template <typename T1>
  static std::optional<uint64_t> exc_of(const Sum1<AE, BE, T1> &e) {
    if (std::holds_alternative<typename Sum1<AE, BE, T1>::Inl1>(e.v())) {
      return std::optional<uint64_t>();
    } else {
      const auto &[a0] = std::get<typename Sum1<AE, BE, T1>::Inr1>(e.v());
      const auto &[a00] = a0;
      return std::make_optional<uint64_t>(a00);
    }
  }

  template <typename T1>
  static top<Sum<uint64_t, T1>>
  run_exc(const Itree<Sum1<AE, BE, crane::obj>, T1> &t) {
    auto &&_sv = t.observe();
    if (std::holds_alternative<
            typename ItreeF<Sum1<AE, BE, crane::obj>, T1,
                            Itree<Sum1<AE, BE, crane::obj>, T1>>::RetF>(
            _sv.v())) {
      const auto &[r0] =
          std::get<typename ItreeF<Sum1<AE, BE, crane::obj>, T1,
                                   Itree<Sum1<AE, BE, crane::obj>, T1>>::RetF>(
              _sv.v());
      return Itree<Sum1<AE, BE, crane::obj>, Sum<uint64_t, T1>>::go(
          ItreeF<Sum1<AE, BE, crane::obj>, Sum<uint64_t, T1>,
                 Itree<Sum1<AE, BE, crane::obj>,
                       Sum<uint64_t, T1>>>::retf(Sum<uint64_t, T1>::inr(r0)));
    } else if (std::holds_alternative<
                   typename ItreeF<Sum1<AE, BE, crane::obj>, T1,
                                   Itree<Sum1<AE, BE, crane::obj>, T1>>::TauF>(
                   _sv.v())) {
      const auto &[t0] =
          std::get<typename ItreeF<Sum1<AE, BE, crane::obj>, T1,
                                   Itree<Sum1<AE, BE, crane::obj>, T1>>::TauF>(
              _sv.v());
      return Itree<Sum1<AE, BE, crane::obj>, Sum<uint64_t, T1>>::lazy_(
          [=]() ->
          typename Itree<Sum1<AE, BE, crane::obj>, Sum<uint64_t, T1>>::Go {
            return {ItreeF<Sum1<AE, BE, crane::obj>, Sum<uint64_t, T1>,
                           Itree<Sum1<AE, BE, crane::obj>,
                                 Sum<uint64_t, T1>>>::tauf(run_exc<T1>(t0))};
          });
    } else {
      const auto &[x, e0] =
          std::get<typename ItreeF<Sum1<AE, BE, crane::obj>, T1,
                                   Itree<Sum1<AE, BE, crane::obj>, T1>>::VisF>(
              _sv.v());
      auto _cs = exc_of(x);
      if (_cs.has_value()) {
        const uint64_t &n = *_cs;
        return Itree<Sum1<AE, BE, crane::obj>, Sum<uint64_t, T1>>::go(
            ItreeF<Sum1<AE, BE, crane::obj>, Sum<uint64_t, T1>,
                   Itree<Sum1<AE, BE, crane::obj>,
                         Sum<uint64_t, T1>>>::retf(Sum<uint64_t, T1>::inl(n)));
      } else {
        return Itree<Sum1<AE, BE, crane::obj>, Sum<uint64_t, T1>>::go(
            ItreeF<Sum1<AE, BE, crane::obj>, Sum<uint64_t, T1>,
                   Itree<Sum1<AE, BE, crane::obj>, Sum<uint64_t, T1>>>::
                visf(x, crane::fn<Itree<Sum1<AE, BE, crane::obj>,
                                        Sum<uint64_t, T1>>(crane::obj)>(
                            [=](const crane::obj &x0)
                                -> Itree<Sum1<AE, BE, crane::obj>,
                                         Sum<uint64_t, T1>> {
                              return run_exc<T1>(crane_call_erased(e0, x0));
                            })));
      }
    }
  }

  static inline const top<uint64_t> ok =
      Itree<Sum1<AE, BE, crane::obj>, uint64_t>::go(
          ItreeF<Sum1<AE, BE, crane::obj>, uint64_t,
                 Itree<Sum1<AE, BE, crane::obj>, uint64_t>>::
              tauf(Itree<Sum1<AE, BE, crane::obj>, uint64_t>::go(
                  ItreeF<Sum1<AE, BE, crane::obj>, uint64_t,
                         Itree<Sum1<AE, BE, crane::obj>, uint64_t>>::
                      tauf(Itree<Sum1<AE, BE, crane::obj>, uint64_t>::go(
                          ItreeF<Sum1<AE, BE, crane::obj>, uint64_t,
                                 Itree<Sum1<AE, BE, crane::obj>,
                                       uint64_t>>::retf(UINT64_C(3)))))));
  static inline const top<uint64_t> raises =
      Itree<Sum1<AE, BE, crane::obj>, uint64_t>::go(
          ItreeF<Sum1<AE, BE, crane::obj>, uint64_t,
                 Itree<Sum1<AE, BE, crane::obj>, uint64_t>>::
              tauf(Itree<Sum1<AE, BE, crane::obj>, uint64_t>::go(
                  ItreeF<Sum1<AE, BE, crane::obj>, uint64_t,
                         Itree<Sum1<AE, BE, crane::obj>, uint64_t>>::
                      visf(Sum1<AE, BE, BE>::inr1(BE::b(UINT64_C(7))),
                           crane::fn<Itree<Sum1<AE, BE, crane::obj>, uint64_t>(
                               crane::obj)>([](const crane::obj &)
                                                -> Itree<
                                                    Sum1<AE, BE, crane::obj>,
                                                    uint64_t> {
                             return Itree<Sum1<AE, BE, crane::obj>, uint64_t>::
                                 go(ItreeF<Sum1<AE, BE, crane::obj>, uint64_t,
                                           Itree<Sum1<AE, BE, crane::obj>,
                                                 uint64_t>>::retf(UINT64_C(0)));
                           })))));
  static uint64_t
  result(uint64_t fuel,
         const Itree<Sum1<AE, BE, crane::obj>, Sum<uint64_t, uint64_t>> &t);
  static inline const uint64_t ok_result =
      result(UINT64_C(10), run_exc<uint64_t>(ok));
  static inline const uint64_t raises_result =
      result(UINT64_C(10), run_exc<uint64_t>(raises));
};

#endif // INCLUDED_ITREE_RET_FAMILY_FROM_RESULT
