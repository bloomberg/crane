#ifndef INCLUDED_FUNCTOR_MODTYPE_VIA_APPLICATION
#define INCLUDED_FUNCTOR_MODTYPE_VIA_APPLICATION

#include "crane_fn.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

struct Nat;
template <typename M, typename X>
concept F_S = requires {
  typename M::u;
  { M::f(std::declval<typename M::u>()) } -> std::same_as<typename X::t>;
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

  Nat add(Nat m) const {
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const Nat *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        auto _value = std::move(m);
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

/// A module type declared in a functor's body, reached through an
/// application of the functor: G.S is the functor's concept F_S over
/// the application's argument, not a member of G.
template <typename M>
concept Base = requires { typename M::t; };

struct FunctorModtypeViaApplication {
  template <Base X> struct F {
    template <F_S<X> Y> struct Use {
      static typename X::t g(typename Y::u x0_) { return Y::f(std::move(x0_)); }
    };
  };

  struct NatB {
    using t = Nat;
  };

  using G = F<NatB>;

  struct YY {
    using u = bool;
    static Nat f(bool b);
  };

  using H = G::Use<YY>;

  template <F_S<NatB> Z> struct K {
    static Nat h(typename Z::u x0_) { return Z::f(std::move(x0_)); }
  };

  using KK = K<YY>;
  static inline const bool res =
      H::g(true).add(KK::h(false)).eqb(Nat::s(Nat::o()));
};

#endif // INCLUDED_FUNCTOR_MODTYPE_VIA_APPLICATION
