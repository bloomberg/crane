#ifndef INCLUDED_INSTANCE_FAMILY_PARAM
#define INCLUDED_INSTANCE_FAMILY_PARAM

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

template <typename I>
concept Functor = requires {
  typename I::template F<crane::obj>;
  {
    I::template fmap<crane::obj, crane::obj>(
        std::declval<crane::fn<crane::obj(crane::obj)>>(),
        std::declval<typename I::template F<crane::obj>>())
  } -> std::convertible_to<typename I::template F<crane::obj>>;
};

struct InstanceFamilyParam {
  template <Functor _tcI0, typename T2, typename T3, typename F0>
  static typename _tcI0::template F<T3>
  fmap(F0 &&x, typename _tcI0::template F<T2> x0) {
    return _tcI0::template fmap<T2, T3>(x, std::move(x0));
  }

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
  static T3 box_rect(F0 &&f, const box<T1, T2> &b0) {
    const auto &[a0] = b0;
    return f(a0);
  }

  template <typename T1, typename T2, typename T3, typename F0>
  static T3 box_rec(F0 &&f, const box<T1, T2> &b0) {
    return box_rect<T1, T2, T3>(f, b0);
  }

  template <typename T1> struct Functor_box {
    template <typename CraneA0> using F = box<T1, CraneA0>;

    template <typename CraneA0, typename CraneA1>
    static box<T1, CraneA1> fmap(crane::fn<CraneA1(CraneA0)> f,
                                 box<T1, CraneA0> b0) {
      const auto &[a0] = b0;
      return box<T1, CraneA1>::box0(f(a0));
    }
  };

  struct noE {
    noE() = delete;
  };

  static inline const box<noE, Nat> b = fmap<Functor_box<noE>, Nat, Nat>(
      [](const Nat &x) { return Nat::s(x); },
      box<noE, Nat>::box0(Nat::s(Nat::s(Nat::o()))));
  static inline const bool is_three = []() {
    const auto &_sv = b;
    const auto &[a] = _sv;
    return a.eqb(Nat::s(Nat::s(Nat::s(Nat::o()))));
  }();
};

#endif // INCLUDED_INSTANCE_FAMILY_PARAM
