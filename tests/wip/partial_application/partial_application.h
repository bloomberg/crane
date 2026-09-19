#ifndef INCLUDED_PARTIAL_APPLICATION
#define INCLUDED_PARTIAL_APPLICATION

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename T> struct Box;

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

template <typename t> using Endo = std::function<t(t)>;

template <typename T1> T1 endo(Endo<T1> endo0, T1 x0_) {
  return endo0(std::move(x0_));
}
template <template <typename> class t>
using TFunctor =
    std::function<t<std::any>(std::function<std::any(std::any)>, t<std::any>)>;

template <template <typename> class T1, typename T2, typename F1,
          typename T3 = std::invoke_result_t<F1 &, T2 &>>
T1<T3> tfmap(TFunctor<T1> tFunctor, F1 &&x, T1<T2> x0) {
  return crane_container_cast<T1<T3>>(
      tFunctor(crane_erase_fn(x), std::move(x0)));
}

template <typename T1> const Endo<T1> Endo_id = [](const auto &x) { return x; };

template <typename T> struct Box {
  // DATA
  Nat tag;
  T t;

  // ACCESSORS
  Box<T> clone() const { return {tag, t}; }

  // CREATORS
  static Box<T> mk(Nat tag, T t) { return {std::move(tag), std::move(t)}; }
};

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T2, F0 &, T1 &>
Box<T2> ft_box(F0 &&f, const Box<T1> &b) {
  const auto &[tag, t0] = b;
  return Box<T2>::mk(endo<Nat>(Endo_id<Nat>, tag), f(t0));
}

Box<std::any> TFunctor_box(Endo<Nat> _x, std::function<std::any(std::any)> x0_,
                           const Box<std::any> &x1_);

template <typename T1, typename T2, typename F1>
  requires std::is_invocable_r_v<T2, F1 &, T1 &>
std::pair<T2, Box<T2>> ft_pair(TFunctor<Box> h, F1 &&f,
                               const std::pair<T1, Box<T1>> &p) {
  const auto &[u, b] = p;
  return std::make_pair(f(u), tfmap(h, f, b));
}

std::pair<std::any, Box<std::any>>
TFunctor_pair(TFunctor<Box> h, std::function<std::any(std::any)> f,
              std::pair<std::any, Box<std::any>> x0_);

struct PartialApplication {
  static std::pair<bool, Box<bool>> convert(const std::pair<Nat, Box<Nat>> &p);
};

#endif // INCLUDED_PARTIAL_APPLICATION
