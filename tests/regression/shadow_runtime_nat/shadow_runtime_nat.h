#ifndef INCLUDED_SHADOW_RUNTIME_NAT
#define INCLUDED_SHADOW_RUNTIME_NAT

#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<::Nat> a0;
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

  static ::Nat o() { return ::Nat(O{}); }

  static ::Nat s(::Nat a0) {
    return ::Nat(S{std::make_shared<::Nat>(std::move(a0))});
  }

  // MANIPULATORS
  ~Nat() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<::Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<::Nat> _cur = _next(v_mut());
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
};

struct ShadowRuntimeNat {
  struct Nat {
    // TYPES
    struct O2 {};

    struct S2 {
      std::shared_ptr<Nat> a0;
    };

    using variant_t = std::variant<O2, S2>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Nat() {}

    explicit Nat(O2 _v) : v_(_v) {}

    explicit Nat(S2 _v) : v_(std::move(_v)) {}

    static Nat o2() { return Nat(O2{}); }

    static Nat s2(Nat a0) {
      return Nat(S2{std::make_shared<Nat>(std::move(a0))});
    }

    // MANIPULATORS
    ~Nat() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
        if (auto *_alt = std::get_if<S2>(&_v)) {
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
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, Nat &, T1 &>
  static T1 Nat_rect(T1 f, F1 &&f0, const Nat &n) {
    if (std::holds_alternative<typename Nat::O2>(n.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename Nat::S2>(n.v());
      return f0(*a0, Nat_rect<T1>(std::move(f), f0, *a0));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, Nat &, T1 &>
  static T1 Nat_rec(T1 f, F1 &&f0, const Nat &n) {
    if (std::holds_alternative<typename Nat::O2>(n.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename Nat::S2>(n.v());
      return f0(*a0, Nat_rec<T1>(std::move(f), f0, *a0));
    }
  }

  static inline const Nat two = Nat::s2(Nat::s2(Nat::o2()));
  static ::Nat toNat(const Nat &n);
  static inline const ::Nat test = toNat(two);
};

#endif // INCLUDED_SHADOW_RUNTIME_NAT
