#ifndef INCLUDED_PARTIAL_APP_CARRIER
#define INCLUDED_PARTIAL_APP_CARRIER

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;

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

struct PartialAppCarrier {
  template <typename s, template <typename> class m, typename a>
  using stateT = crane::fn<m<std::pair<s, a>>(s)>;

  template <typename E, typename A> struct box {
    // DATA
    A a;

    // ACCESSORS
    box<E, A> clone() const { return {a}; }

    template <typename CraneU0, typename CraneU1>
    operator box<CraneU0, CraneU1>() const {
      return {[&]() -> CraneU1 {
        if constexpr (crane_convertible<CraneU1, const A &>) {
          return crane_convert<CraneU1>(a);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }

    // CREATORS
    static box<E, A> box0(A a) { return {std::move(a)}; }
  };

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, const T2 &>
  static T3 box_rect(F0 &&f, const box<T1, T2> &b) {
    const auto &[a0] = b;
    return f(a0);
  }

  template <typename T1, typename T2, typename T3, typename F0>
  static T3 box_rec(F0 &&f, const box<T1, T2> &b) {
    return box_rect<T1, T2, T3>(f, b);
  }

  struct noE {
    noE() = delete;
  };

  template <typename CraneP0> struct crane_carrier_tch {
    template <typename CraneTcArg> using c = box<CraneP0, CraneTcArg>;
  };

  template <typename T1>
  static const stateT<Nat, crane_carrier_tch<T1>::template c, Nat> &get_st() {
    static const stateT<Nat, crane_carrier_tch<T1>::template c, Nat> v =
        [](const Nat &s) {
          return box<T1, std::pair<Nat, Nat>>::box0(std::make_pair(s, s));
        };
    return v;
  }

  static inline const box<noE, std::pair<Nat, Nat>> r =
      get_st<noE>()(Nat::s(Nat::s(Nat::s(Nat::o()))));

  static inline const bool is_three = []() {
    const auto &_sv = r;
    const auto &[a] = _sv;
    const auto &[a1, _x] = a;
    return a1.eqb(Nat::s(Nat::s(Nat::s(Nat::o()))));
  }();
};

#endif // INCLUDED_PARTIAL_APP_CARRIER
