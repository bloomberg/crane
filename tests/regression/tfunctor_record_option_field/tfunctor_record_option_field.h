#ifndef INCLUDED_TFUNCTOR_RECORD_OPTION_FIELD
#define INCLUDED_TFUNCTOR_RECORD_OPTION_FIELD

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <memory>
#include <optional>
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

  Nat add(Nat m) const {
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<Nat>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = typename Nat::S(nullptr);
        Nat &_node =
            (_write ? *(*_write = std::make_shared<Nat>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename Nat::S>(_node.v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct TfunctorRecordOptionField {
  template <typename t>
  using TFunctor = crane::fn<t(crane::fn<crane::obj(crane::obj)>, t)>;

  template <typename T1, typename T2, typename T3, typename F1>
  static crane::rebind_t<T1, T3>
  tfmap(std::type_identity_t<TFunctor<T1>> tFunctor, F1 &&f,
        crane::rebind_t<T1, T2> x) {
    return crane_container_cast<crane::rebind_t<T1, T3>>(
        tFunctor(crane_erase_fn(f), crane_convert<T1>(std::move(x))));
  }

  template <typename T1, typename F1>
  static std::optional<T1> TFunctor_option(std::type_identity_t<TFunctor<T1>> h,
                                           F1 &&f,
                                           const std::optional<T1> &ot) {
    if (ot.has_value()) {
      const auto &t = *ot;
      return std::make_optional<T1>(
          tfmap<T1, crane::obj, crane::obj>(std::move(h), f, t));
    } else {
      return std::optional<T1>();
    }
  }

  template <typename T> struct exp {
    // TYPES
    struct Lit {
      T t;
    };

    struct Neg {
      std::shared_ptr<exp<T>> e;
    };

    using variant_t = std::variant<Lit, Neg>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    exp() {}

    explicit exp(Lit _v) : v_(std::move(_v)) {}

    explicit exp(Neg _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    exp(const exp<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename exp<CraneU>::Lit>(_other.v())) {
              const auto &[t] = std::get<typename exp<CraneU>::Lit>(_other.v());
              return Lit{[&]() -> T {
                if constexpr (crane_convertible<T, const CraneU &>) {
                  return crane_convert<T>(t);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              const auto &[e] = std::get<typename exp<CraneU>::Neg>(_other.v());
              return Neg{
                  (e ? std::make_shared<exp<T>>(crane_convert<exp<T>>(*e))
                     : nullptr)};
            }
          }()) {}

    static exp<T> lit(T t) { return exp<T>(Lit{std::move(t)}); }

    static exp<T> neg(exp<T> e) {
      return exp<T>(Neg{std::make_shared<exp<T>>(std::move(e))});
    }

    // MANIPULATORS
    ~exp() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<exp<T>> {
        if (auto *_alt = std::get_if<Neg>(&_v)) {
          if (_alt->e && _alt->e.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->e);
          }
        }
        return nullptr;
      };
      std::shared_ptr<exp<T>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    exp(const exp &) = default;
    exp &operator=(const exp &) = default;
    exp(exp &&) = default;
    exp &operator=(exp &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<T2, F0 &, const T1 &>
  static T2 exp_rect(F0 &&f, F1 &&f0, const exp<T1> &e) {
    if (std::holds_alternative<typename exp<T1>::Lit>(e.v())) {
      const auto &[t0] = std::get<typename exp<T1>::Lit>(e.v());
      return f(t0);
    } else {
      const auto &[e1] = std::get<typename exp<T1>::Neg>(e.v());
      return f0(*e1, exp_rect<T1, T2>(f, f0, *e1));
    }
  }

  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<T2, F0 &, const T1 &>
  static T2 exp_rec(F0 &&f, F1 &&f0, const exp<T1> &e) {
    if (std::holds_alternative<typename exp<T1>::Lit>(e.v())) {
      const auto &[t0] = std::get<typename exp<T1>::Lit>(e.v());
      return f(t0);
    } else {
      const auto &[e1] = std::get<typename exp<T1>::Neg>(e.v());
      return f0(*e1, exp_rec<T1, T2>(f, f0, *e1));
    }
  }

  template <typename T> struct global {
    T g_typ;
    std::optional<exp<T>> g_exp;

    // ACCESSORS
    template <typename CraneU> operator global<CraneU>() const {
      return {[&]() -> CraneU {
                if constexpr (crane_convertible<CraneU, const T &>) {
                  return crane_convert<CraneU>(g_typ);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }(),
              std::optional<exp<CraneU>>(g_exp)};
    }
  };

  static exp<crane::obj> TFunctor_exp(crane::fn<crane::obj(crane::obj)> f,
                                      const exp<crane::obj> &e);
  static global<crane::obj> TFunctor_global(crane::fn<crane::obj(crane::obj)> f,
                                            const global<crane::obj> &g);
  static inline const global<Nat> g0 = global<Nat>{
      Nat::s(Nat::o()),
      std::make_optional<exp<Nat>>(exp<Nat>::lit(Nat::s(Nat::s(Nat::o()))))};
  static inline const global<Nat> g1 = tfmap<global<crane::obj>, Nat, Nat>(
      [](auto &&_ec0, global<crane::obj> _ec1) {
        return TFunctor_global(_ec0, _ec1);
      },
      [](const Nat &x) { return Nat::s(x); }, g0);
  static constexpr bool is_five = true;
};

#endif // INCLUDED_TFUNCTOR_RECORD_OPTION_FIELD
