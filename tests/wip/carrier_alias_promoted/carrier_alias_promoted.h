#ifndef INCLUDED_CARRIER_ALIAS_PROMOTED
#define INCLUDED_CARRIER_ALIAS_PROMOTED

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename E, typename R, typename itree> struct ItreeF;
template <typename E, typename R> struct Itree;

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

  Nat add(Nat m) const {
    std::shared_ptr<Nat> _head{};
    std::shared_ptr<Nat> *_write = &_head;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        *_write = std::make_shared<Nat>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = std::make_shared<Nat>(typename Nat::S(nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename Nat::S>((*_write)->v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_head);
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

  const ItreeF<E, R, Itree<E, R>> &observe() const & {
    const auto &[_observe] = std::get<typename Itree<E, R>::Go>(this->v());
    return _observe;
  }

  ItreeF<E, R, Itree<E, R>> observe() const && {
    const auto &[_observe] = std::get<typename Itree<E, R>::Go>(this->v());
    return _observe;
  }
};

template <typename
I>concept Params = requires {
    typename I::ptr;
  } && (requires {
    { I::zero() } -> std::convertible_to<typename I::ptr>;
  } || requires {
    { I::zero } -> std::convertible_to<typename I::ptr>;
  });

struct CarrierAliasPromoted {
  template <typename s, template <typename> class m, typename a>
  using stateT = crane::fn<m<std::pair<s, a>>(s)>;
  using ptr = crane::obj;

  template <typename ptr> struct memE {
    // DATA
    ptr a0;

    // ACCESSORS
    memE<ptr> clone() const { return {a0}; }

    template <typename _U> operator memE<_U>() const { return {a0}; }

    // CREATORS
    static memE<ptr> load(ptr a0) { return {std::move(a0)}; }
  };

  template <typename _P0> struct _crane_carrier_tch {
    template <typename _CraneTcArg>
    using c = Itree<memE<typename _P0::ptr>, _CraneTcArg>;
  };

  template <Params _tcI0>
  static stateT<Nat, _crane_carrier_tch<_tcI0>::template c, Nat> get_st(Nat n) {
    return [=](const Nat &s) {
      return Itree<memE<typename _tcI0::ptr>, std::pair<Nat, Nat>>::lazy_(
          [=]() -> Itree<memE<typename _tcI0::ptr>, std::pair<Nat, Nat>> {
            return Itree<memE<typename _tcI0::ptr>, std::pair<Nat, Nat>>::go(
                ItreeF<memE<typename _tcI0::ptr>, std::pair<Nat, Nat>,
                       Itree<memE<typename _tcI0::ptr>, std::pair<Nat, Nat>>>::
                    retf(std::make_pair(s.add(n), s)));
          });
    };
  }

  struct natParams {
    using ptr = Nat;

    static Nat zero() { return Nat::o(); }
  };

  static_assert(Params<natParams>);
  static inline const Itree<memE<typename natParams::ptr>, std::pair<Nat, Nat>>
      r = crane::any_cast<
          Itree<memE<typename natParams::ptr>, std::pair<Nat, Nat>>>(
          get_st<natParams>(Nat::s(Nat::o()))(Nat::s(Nat::s(Nat::o()))));

  static inline const bool is_three = []() {
    auto &&_sv = r.observe();
    if (std::holds_alternative<
            typename ItreeF<memE<ptr>, std::pair<Nat, Nat>,
                            Itree<memE<ptr>, std::pair<Nat, Nat>>>::RetF>(
            _sv.v())) {
      const auto &[r1] = std::get<
          typename ItreeF<memE<ptr>, std::pair<Nat, Nat>,
                          Itree<memE<ptr>, std::pair<Nat, Nat>>>::RetF>(
          _sv.v());
      const auto &[a, _x] = r1;
      return a.eqb(Nat::s(Nat::s(Nat::s(Nat::o()))));
    } else {
      return false;
    }
  }();
};

#endif // INCLUDED_CARRIER_ALIAS_PROMOTED
