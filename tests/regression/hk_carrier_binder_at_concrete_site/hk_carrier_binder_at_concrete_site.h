#ifndef INCLUDED_HK_CARRIER_BINDER_AT_CONCRETE_SITE
#define INCLUDED_HK_CARRIER_BINDER_AT_CONCRETE_SITE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename T> struct box;
template <typename T, typename Body> struct holder;

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

  bool ltb(const Nat &m) const { return Nat::s(*this).leb(m); }

  bool leb(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        return true;
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

template <typename t>
using TFunctor = crane::fn<t(crane::fn<crane::obj(crane::obj)>, t)>;

template <typename T1, typename T2, typename T3, typename F1>
crane::rebind_t<T1, T3> tfmap(std::type_identity_t<TFunctor<T1>> tFunctor,
                              F1 &&f, crane::rebind_t<T1, T2> x) {
  return crane_container_cast<crane::rebind_t<T1, T3>>(
      tFunctor(crane_erase_fn(f), crane_convert<T1>(std::move(x))));
}

template <typename T> struct box {
  T b_payload;

  // ACCESSORS
  template <typename _U> operator box<_U>() const {
    return {[&]() -> _U {
      if constexpr (crane_convertible<_U, const T &>) {
        return crane_convert<_U>(b_payload);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }
};

box<crane::obj> TFunctor_box(crane::fn<crane::obj(crane::obj)> f,
                             const box<crane::obj> &b);

template <typename T, typename Body> struct holder {
  T h_head;
  Body h_body;

  // ACCESSORS
  template <typename _U0, typename _U1> operator holder<_U0, _U1>() const {
    return {[&]() -> _U0 {
              if constexpr (crane_convertible<_U0, const T &>) {
                return crane_convert<_U0>(h_head);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> _U1 {
              if constexpr (crane_convertible<_U1, const Body &>) {
                return crane_convert<_U1>(h_body);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }
};

template <typename T1, typename F1>
holder<crane::obj, T1> TFunctor_holder(std::type_identity_t<TFunctor<T1>> h,
                                       F1 &&f,
                                       const holder<crane::obj, T1> &m) {
  return holder<crane::obj, T1>{f(m.h_head), tfmap<T1, crane::obj, crane::obj>(
                                                 std::move(h), f, m.h_body)};
}
template <template <typename> class f>
using Convert = crane::fn<f<bool>(Nat, f<Nat>)>;

template <template <typename> class T1>
T1<bool> convert(std::type_identity_t<Convert<T1>> convert0, const Nat &x0_,
                 T1<Nat> x1_) {
  return crane_container_cast<T1<bool>>(convert0(x0_, std::move(x1_)));
}

template <typename _CraneTcArg>
using _crane_carrier_tc_904911fedcfba566 =
    holder<_CraneTcArg, box<_CraneTcArg>>;
const Convert<_crane_carrier_tc_904911fedcfba566> Convert_holder =
    [](Nat n, const holder<Nat, box<Nat>> &eta0_) {
      return tfmap<holder<crane::obj, box<crane::obj>>, Nat, bool>(
          []() {
            return [](crane::fn<crane::obj(crane::obj)> _x0,
                      const auto &_x1) -> holder<crane::obj, box<crane::obj>> {
              return TFunctor_holder<box<crane::obj>>(
                  [](auto &&_ec0, box<crane::obj> _ec1) {
                    return TFunctor_box(_ec0, _ec1);
                  },
                  _x0, crane_convert<holder<crane::obj, box<crane::obj>>>(_x1));
            };
          }(),
          [=](const Nat &x) { return n.ltb(x); }, eta0_);
    };
holder<bool, box<bool>> run(const holder<Nat, box<Nat>> &m);

#endif // INCLUDED_HK_CARRIER_BINDER_AT_CONCRETE_SITE
