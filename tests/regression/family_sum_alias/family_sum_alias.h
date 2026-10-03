#ifndef INCLUDED_FAMILY_SUM_ALIAS
#define INCLUDED_FAMILY_SUM_ALIAS

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename E, typename R, typename itree> struct ItreeF;
template <typename E, typename R> struct Itree;
template <typename E1, typename E2, typename X> struct Sum1;

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
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

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

  template <typename _U0, typename _U1, typename _U2>
  ItreeF(const ItreeF<_U0, _U1, _U2> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename ItreeF<_U0, _U1, _U2>::RetF>(
                  _other.v())) {
            const auto &[r] =
                std::get<typename ItreeF<_U0, _U1, _U2>::RetF>(_other.v());
            return RetF{[&]() -> R {
              if constexpr (crane_convertible<R, const _U1 &>) {
                return crane_convert<R>(r);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            if (std::holds_alternative<typename ItreeF<_U0, _U1, _U2>::TauF>(
                    _other.v())) {
              const auto &[t] =
                  std::get<typename ItreeF<_U0, _U1, _U2>::TauF>(_other.v());
              return TauF{[&]() -> itree {
                if constexpr (crane_convertible<itree, const _U2 &>) {
                  return crane_convert<itree>(t);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              const auto &[x, e] =
                  std::get<typename ItreeF<_U0, _U1, _U2>::VisF>(_other.v());
              return VisF{[&]() -> E {
                            if constexpr (crane_convertible<E, const _U0 &>) {
                              return crane_convert<E>(x);
                            } else {
                              throw std::logic_error(
                                  "unreachable: inactive constructor field at "
                                  "this instantiation");
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
  template <typename _S0 = Itree<E, R>> struct Go_ {
    ItreeF<E, R, _S0> _observe;
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

  template <typename _U0, typename _U1>
  Itree(const Itree<_U0, _U1> &_other)
      : lazy_v_(crane::lazy<variant_t>::converted_from(
            _other.lazy_cell(), [=]() -> variant_t {
              const auto &[_observe] =
                  std::get<typename Itree<_U0, _U1>::Go>(_other.v());
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

  template <typename _U0, typename _U1, typename _U2>
  Sum1(const Sum1<_U0, _U1, _U2> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sum1<_U0, _U1, _U2>::Inl1>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Sum1<_U0, _U1, _U2>::Inl1>(_other.v());
            return Inl1{[&]() -> E1 {
              if constexpr (crane_convertible<E1, const _U0 &>) {
                return crane_convert<E1>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum1<_U0, _U1, _U2>::Inr1>(_other.v());
            return Inr1{[&]() -> E2 {
              if constexpr (crane_convertible<E2, const _U1 &>) {
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

struct FamilySumAlias {
  template <typename P> struct aE {
    // DATA
    P a0;

    // ACCESSORS
    aE<P> clone() const { return {a0}; }

    template <typename _U> operator aE<_U>() const {
      return {[&]() -> _U {
        if constexpr (crane_convertible<_U, const P &>) {
          return crane_convert<_U>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }

    // CREATORS
    static aE<P> a(P a0) { return {std::move(a0)}; }
  };
  enum class BE { B };
  enum class CE { C };
  template <typename p, typename x>
  using AllE = Sum1<aE<p>, Sum1<BE, CE, crane::obj>, x>;
  static inline const Itree<AllE<Nat, crane::obj>, Nat> t =
      Itree<AllE<Nat, crane::obj>, Nat>::go(
          ItreeF<
              Sum1<aE<Nat>, Sum1<BE, CE, crane::obj>, crane::obj>, Nat,
              Itree<Sum1<aE<Nat>, Sum1<BE, CE, crane::obj>, crane::obj>, Nat>>::
              visf(
                  Sum1<aE<Nat>, Sum1<BE, CE, crane::obj>, aE<Nat>>::inl1(
                      aE<Nat>::a(Nat::s(Nat::s(Nat::s(Nat::o()))))),
                  crane::fn<Itree<
                      Sum1<aE<Nat>, Sum1<BE, CE, crane::obj>, crane::obj>, Nat>(
                      crane::obj)>([](const crane::obj &n)
                                       -> Itree<Sum1<aE<Nat>,
                                                     Sum1<BE, CE, crane::obj>,
                                                     crane::obj>,
                                                Nat> {
                    return Itree<
                        Sum1<aE<Nat>, Sum1<BE, CE, crane::obj>, crane::obj>,
                        Nat>::
                        go(ItreeF<
                            Sum1<aE<Nat>, Sum1<BE, CE, crane::obj>, crane::obj>,
                            Nat,
                            Itree<Sum1<aE<Nat>, Sum1<BE, CE, crane::obj>,
                                       crane::obj>,
                                  Nat>>::retf(crane::any_cast<Nat>(n)));
                  })));
  static inline const bool is_three = []() {
    auto &&_sv = []() {
      auto &&_sv0 = t;
      const auto &[_observe0] = std::get<typename Itree<
          Sum1<aE<Nat>, Sum1<BE, CE, crane::obj>, crane::obj>, Nat>::Go>(
          _sv0.v());
      return _observe0;
    }();
    if (std::holds_alternative<typename ItreeF<
            Sum1<aE<Nat>, Sum1<BE, CE, crane::obj>, crane::obj>, Nat,
            Itree<Sum1<aE<Nat>, Sum1<BE, CE, crane::obj>, crane::obj>,
                  Nat>>::VisF>(_sv.v())) {
      const auto &[x, e0] = std::get<typename ItreeF<
          Sum1<aE<Nat>, Sum1<BE, CE, crane::obj>, crane::obj>, Nat,
          Itree<Sum1<aE<Nat>, Sum1<BE, CE, crane::obj>, crane::obj>,
                Nat>>::VisF>(_sv.v());
      if (std::holds_alternative<typename Sum1<
              aE<Nat>, Sum1<BE, CE, crane::obj>, crane::obj>::Inl1>(x.v())) {
        const auto &[a01] = std::get<
            typename Sum1<aE<Nat>, Sum1<BE, CE, crane::obj>, crane::obj>::Inl1>(
            x.v());
        const auto &[a02] = a01;
        return crane::any_cast<Nat>(a02).eqb(Nat::s(Nat::s(Nat::s(Nat::o()))));
      } else {
        return false;
      }
    } else {
      return false;
    }
  }();
};

#endif // INCLUDED_FAMILY_SUM_ALIAS
