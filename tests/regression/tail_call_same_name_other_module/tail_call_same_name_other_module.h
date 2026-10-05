#ifndef INCLUDED_TAIL_CALL_SAME_NAME_OTHER_MODULE
#define INCLUDED_TAIL_CALL_SAME_NAME_OTHER_MODULE

#include "crane_fn.h"
#include <atomic>
#include <memory>
#include <optional>
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

struct TailCallSameNameOtherModule {
  struct T1 {
    struct t1 {
      // TYPES
      struct Z1 {};

      struct C1 {
        Nat a0;
      };

      using variant_t = std::variant<Z1, C1>;

    private:
      // DATA
      variant_t v_;

    public:
      // CREATORS
      t1() {}

      explicit t1(Z1 _v) : v_(_v) {}

      explicit t1(C1 _v) : v_(std::move(_v)) {}

      static t1 z1() { return t1(Z1{}); }

      static t1 c1(Nat a0) { return t1(C1{std::move(a0)}); }

      // MANIPULATORS
      inline variant_t &v_mut() { return v_; }

      // ACCESSORS
      const variant_t &v() const { return v_; }

      template <typename T1, typename F1>
        requires std::is_invocable_r_v<T1, F1 &, const Nat &>
      T1 t1_rect(T1 f, F1 &&f0) const {
        if (std::holds_alternative<typename t1::Z1>(this->v())) {
          return f;
        } else {
          const auto &[a0] = std::get<typename t1::C1>(this->v());
          return f0(a0);
        }
      }

      template <typename T1, typename F1>
        requires std::is_invocable_r_v<T1, F1 &, const Nat &>
      T1 t1_rec(T1 f, F1 &&f0) const {
        if (std::holds_alternative<typename t1::Z1>(this->v())) {
          return f;
        } else {
          const auto &[a0] = std::get<typename t1::C1>(this->v());
          return f0(a0);
        }
      }

      Nat cmp(const t1 &y) const {
        if (std::holds_alternative<typename t1::Z1>(this->v())) {
          return Nat::o();
        } else {
          const auto &[a0] = std::get<typename t1::C1>(this->v());
          if (std::holds_alternative<typename t1::Z1>(y.v())) {
            return Nat::o();
          } else {
            const auto &[a00] = std::get<typename t1::C1>(y.v());
            return a0.add(a00);
          }
        }
      }
    };
  };

  struct T2 {
    struct t2 {
      // TYPES
      struct Z2 {};

      struct C2 {
        Nat a0;
      };

      using variant_t = std::variant<Z2, C2>;

    private:
      // DATA
      variant_t v_;

    public:
      // CREATORS
      t2() {}

      explicit t2(Z2 _v) : v_(_v) {}

      explicit t2(C2 _v) : v_(std::move(_v)) {}

      static t2 z2() { return t2(Z2{}); }

      static t2 c2(Nat a0) { return t2(C2{std::move(a0)}); }

      // MANIPULATORS
      inline variant_t &v_mut() { return v_; }

      // ACCESSORS
      const variant_t &v() const { return v_; }

      template <typename T1, typename F1>
        requires std::is_invocable_r_v<T1, F1 &, const Nat &>
      T1 t2_rect(T1 f, F1 &&f0) const {
        if (std::holds_alternative<typename t2::Z2>(this->v())) {
          return f;
        } else {
          const auto &[a0] = std::get<typename t2::C2>(this->v());
          return f0(a0);
        }
      }

      template <typename T1, typename F1>
        requires std::is_invocable_r_v<T1, F1 &, const Nat &>
      T1 t2_rec(T1 f, F1 &&f0) const {
        if (std::holds_alternative<typename t2::Z2>(this->v())) {
          return f;
        } else {
          const auto &[a0] = std::get<typename t2::C2>(this->v());
          return f0(a0);
        }
      }

      T1::t1 to1() const {
        if (std::holds_alternative<typename t2::Z2>(this->v())) {
          return T1::t1::z1();
        } else {
          const auto &[a0] = std::get<typename t2::C2>(this->v());
          return T1::t1::c1(a0);
        }
      }

      Nat cmp(const t2 &y) const { return this->to1().cmp(y.to1()); }
    };
  };

  static inline const Nat go =
      T2::t2::c2(Nat::s(Nat::o())).cmp(T2::t2::c2(Nat::s(Nat::s(Nat::o()))));

  static inline const bool ok = go.eqb(Nat::s(Nat::s(Nat::s(Nat::o()))));
};

#endif // INCLUDED_TAIL_CALL_SAME_NAME_OTHER_MODULE
