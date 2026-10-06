#ifndef INCLUDED_PARTIAL_APPLICATION
#define INCLUDED_PARTIAL_APPLICATION

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename T1> struct Endo_id;
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

template <typename I, typename T>
concept Endo = requires {
  { I::endo(std::declval<T>()) } -> std::convertible_to<T>;
};

template <typename _tcI0, typename T1>
  requires Endo<_tcI0, T1>
T1 endo(T1 x0_) {
  return _tcI0::endo(std::move(x0_));
}

template <typename I>
concept TFunctor = requires {
  typename I::template T<crane::obj>;
  {
    I::template tfmap<crane::obj, crane::obj>(
        std::declval<crane::fn<crane::obj(crane::obj)>>(),
        std::declval<typename I::template T<crane::obj>>())
  } -> std::convertible_to<typename I::template T<crane::obj>>;
};

template <TFunctor _tcI0, typename T2, typename T3, typename F0>
typename _tcI0::template T<T3> tfmap(F0 &&x,
                                     typename _tcI0::template T<T2> x0) {
  return _tcI0::template tfmap<T2, T3>(x, std::move(x0));
}

template <typename T1> struct Endo_id {
  static T1 endo(T1 x) { return x; }
};

template <typename T> struct Box {
  // DATA
  Nat tag;
  T t;

  // ACCESSORS
  Box<T> clone() const { return {tag, t}; }

  template <typename CraneU> operator Box<CraneU>() const {
    return {tag, [&]() -> CraneU {
              if constexpr (crane_convertible<CraneU, const T &>) {
                return crane_convert<CraneU>(t);
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
  requires std::is_invocable_r_v<T2, F0 &, const T1 &>
Box<T2> ft_box(F0 &&f, const Box<T1> &b) {
  const auto &[tag, t0] = b;
  return Box<T2>::mk(Endo_id<Nat>::endo(tag), f(t0));
}

template <typename _tcI0>
  requires Endo<_tcI0, Nat>
struct TFunctor_box {
  template <typename CraneA0> using T = Box<CraneA0>;

  template <typename CraneA0, typename CraneA1>
  static Box<CraneA1> tfmap(crane::fn<CraneA1(CraneA0)> a0, Box<CraneA0> a1) {
    return ft_box<CraneA0, CraneA1>(std::move(a0), std::move(a1));
  }
};

template <TFunctor _tcI0, typename T1, typename T2, typename F0>
std::pair<T2, Box<T2>> ft_pair(F0 &&f, const std::pair<T1, Box<T1>> &p) {
  const auto &[u, b] = p;
  return std::make_pair(f(u), _tcI0::template tfmap<T1, T2>(f, b));
}

template <TFunctor _tcI0> struct TFunctor_pair {
  template <typename CraneA0> using T = std::pair<CraneA0, Box<CraneA0>>;

  template <typename CraneA0, typename CraneA1>
  static std::pair<CraneA1, Box<CraneA1>>
  tfmap(crane::fn<CraneA1(CraneA0)> a0, std::pair<CraneA0, Box<CraneA0>> a1) {
    return ft_pair<_tcI0, CraneA0, CraneA1>(std::move(a0), std::move(a1));
  }
};

#endif // INCLUDED_PARTIAL_APPLICATION
