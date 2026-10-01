#ifndef INCLUDED_PARTIAL_APPLICATION
#define INCLUDED_PARTIAL_APPLICATION

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename T> struct Box;

struct PartialApplication {
  static std::pair<bool, Box<bool>> convert(const std::pair<Nat, Box<Nat>> &p);
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

template <typename t> using Endo = crane::fn<t(t)>;

template <typename T1> T1 endo(std::type_identity_t<Endo<T1>> endo0, T1 x0_) {
  return endo0(std::move(x0_));
}

template <typename t>
using TFunctor = crane::fn<t(crane::fn<crane::obj(crane::obj)>, t)>;

template <typename T1, typename T2, typename T3, typename F1>
crane::rebind_t<T1, T3> tfmap(std::type_identity_t<TFunctor<T1>> tFunctor,
                              F1 &&x, crane::rebind_t<T1, T2> x0) {
  return crane_container_cast<crane::rebind_t<T1, T3>>(
      tFunctor(crane_erase_fn(x), crane_convert<T1>(std::move(x0))));
}

template <typename T1> const Endo<T1> Endo_id = [](const auto &x) { return x; };

template <typename T> struct Box {
  // DATA
  Nat tag;
  T t;

  // ACCESSORS
  Box<T> clone() const { return {tag, t}; }

  template <typename _U> operator Box<_U>() const {
    return {tag, [&]() -> _U {
              if constexpr (crane_convertible<_U, const T &>) {
                return crane_convert<_U>(t);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static Box<T> mk(Nat tag, T t) { return {std::move(tag), std::move(t)}; }
};

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T2, F0 &, T1 &>
Box<T2> ft_box(F0 &&f, const Box<T1> &b) {
  const auto &[tag, t0] = b;
  return Box<T2>::mk(endo<Nat>(Endo_id<Nat>, tag), f(t0));
}

Box<crane::obj> TFunctor_box(Endo<Nat> _x,
                             crane::fn<crane::obj(crane::obj)> x0_,
                             const Box<crane::obj> &x1_);

template <typename T1, typename T2, typename F1>
  requires std::is_invocable_r_v<T2, F1 &, T1 &>
std::pair<T2, Box<T2>> ft_pair(TFunctor<Box<crane::obj>> h, F1 &&f,
                               const std::pair<T1, Box<T1>> &p) {
  const auto &[u, b] = p;
  return std::make_pair(f(u), tfmap<Box<crane::obj>, T1, T2>(h, f, b));
}

std::pair<crane::obj, Box<crane::obj>>
TFunctor_pair(TFunctor<Box<crane::obj>> h, crane::fn<crane::obj(crane::obj)> f,
              std::pair<crane::obj, Box<crane::obj>> x0_);

#endif // INCLUDED_PARTIAL_APPLICATION
