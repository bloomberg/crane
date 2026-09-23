#ifndef INCLUDED_HK_CARRIER_BINDER_AT_CONCRETE_SITE
#define INCLUDED_HK_CARRIER_BINDER_AT_CONCRETE_SITE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
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
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool ltb(const Nat &m) const { return Nat::s(std::move(*this)).leb(m); }

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
template <template <typename> class t>
using TFunctor =
    std::function<t<std::any>(std::function<std::any(std::any)>, t<std::any>)>;

template <template <typename> class T1, typename T2, typename F1,
          typename T3 = std::invoke_result_t<F1 &, T2 &>>
T1<T3> tfmap(std::type_identity_t<TFunctor<T1>> tFunctor, F1 &&f, T1<T2> x) {
  return crane_container_cast<T1<T3>>(
      tFunctor(crane_erase_fn(f), crane_convert<T1<std::any>>(std::move(x))));
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

box<std::any> TFunctor_box(std::function<std::any(std::any)> f,
                           const box<std::any> &b);

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

template <template <typename> class T1, typename F1>
holder<std::any, T1<std::any>>
TFunctor_holder(std::type_identity_t<TFunctor<T1>> h, F1 &&f,
                const holder<std::any, T1<std::any>> &m) {
  return holder<std::any, T1<std::any>>{
      f(m.h_head), tfmap<T1, std::any>(std::move(h), f, m.h_body)};
}
template <template <typename> class f>
using Convert = std::function<f<bool>(Nat, f<Nat>)>;

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
      return tfmap<_crane_carrier_tc_904911fedcfba566>(
          []() {
            return [](std::function<std::any(std::any)> _x0,
                      holder<std::any, box<std::any>> _x1)
                       -> holder<std::any, box<std::any>> {
              return TFunctor_holder<box>(
                  [](auto &&_ec0, box<std::any> _ec1) {
                    return TFunctor_box(_ec0, _ec1);
                  },
                  _x0, _x1);
            };
          }(),
          [=](const Nat &x) mutable { return n.ltb(x); }, eta0_);
    };
holder<bool, box<bool>> run(const holder<Nat, box<Nat>> &m);

#endif // INCLUDED_HK_CARRIER_BINDER_AT_CONCRETE_SITE
