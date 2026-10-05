#ifndef INCLUDED_TFUNCTOR_ALIAS_CARRIER
#define INCLUDED_TFUNCTOR_ALIAS_CARRIER

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

struct TfunctorAliasCarrier {
  template <typename t>
  using TFunctor = crane::fn<t(crane::fn<crane::obj(crane::obj)>, t)>;

  template <typename T1, typename T2, typename T3, typename F1>
  static crane::rebind_t<T1, T3>
  tfmap(std::type_identity_t<TFunctor<T1>> tFunctor, F1 &&f,
        crane::rebind_t<T1, T2> x) {
    return crane_container_cast<crane::rebind_t<T1, T3>>(
        tFunctor(crane_erase_fn(f), crane_convert<T1>(std::move(x))));
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
        : v_(crane_convert_spine(
              _other, std::shared_ptr<exp<T>>(nullptr),
              [](const exp<CraneU> &_cell) -> const exp<CraneU> * {
                if (std::holds_alternative<typename exp<CraneU>::Neg>(
                        _cell.v())) {
                  return std::get<typename exp<CraneU>::Neg>(_cell.v()).e.get();
                } else {
                  return nullptr;
                }
              },
              [&](const exp<CraneU> &_other,
                  std::shared_ptr<exp<T>> _below) -> variant_t {
                if (std::holds_alternative<typename exp<CraneU>::Lit>(
                        _other.v())) {
                  const auto &[t] =
                      std::get<typename exp<CraneU>::Lit>(_other.v());
                  return Lit{[&]() -> T {
                    if constexpr (crane_convertible<T, const CraneU &>) {
                      return crane_convert<T>(t);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }()};
                } else {
                  const auto &[e] =
                      std::get<typename exp<CraneU>::Neg>(_other.v());
                  return Neg{std::move(_below)};
                }
              },
              [](auto &&_alt) {
                return std::make_shared<exp<T>>(std::move(_alt));
              })) {}

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
  static T2 exp_rec(F0 &&f, F1 &&f0, const exp<T1> &e) {
    return exp_rect<T1, T2>(f, f0, e);
  }

  template <typename t> using texp = std::pair<t, exp<t>>;

  template <typename T> struct cmpxchg {
    texp<T> c_ptr;
    texp<T> c_new;

    // ACCESSORS
    template <typename CraneU> operator cmpxchg<CraneU>() const {
      return {crane_convert<texp<CraneU>>(c_ptr),
              crane_convert<texp<CraneU>>(c_new)};
    }
  };

  static exp<crane::obj> TFunctor_exp(crane::fn<crane::obj(crane::obj)> f,
                                      const exp<crane::obj> &e);
  static texp<crane::obj>
  TFunctor_texp(TFunctor<exp<crane::obj>> h,
                crane::fn<crane::obj(crane::obj)> f,
                const std::pair<crane::obj, exp<crane::obj>> &pat);
  static cmpxchg<crane::obj>
  TFunctor_cmpxchg(crane::fn<crane::obj(crane::obj)> f,
                   const cmpxchg<crane::obj> &c);
  static inline const cmpxchg<Nat> c0 = cmpxchg<Nat>{
      std::make_pair(Nat::s(Nat::o()), exp<Nat>::lit(Nat::s(Nat::o()))),
      std::make_pair(Nat::s(Nat::s(Nat::o())),
                     exp<Nat>::neg(exp<Nat>::lit(Nat::s(Nat::s(Nat::o())))))};
  static inline const cmpxchg<Nat> c1 = tfmap<cmpxchg<crane::obj>, Nat, Nat>(
      [](auto &&_ec0, cmpxchg<crane::obj> _ec1) {
        return TFunctor_cmpxchg(_ec0, _ec1);
      },
      [](const Nat &x) { return Nat::s(x); }, c0);
  static inline const bool is_five =
      c1.c_ptr.first.add(c1.c_new.first)
          .eqb(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))));
};

#endif // INCLUDED_TFUNCTOR_ALIAS_CARRIER
