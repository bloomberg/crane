#ifndef INCLUDED_SELF_PARTIAL_APP_IN_LET
#define INCLUDED_SELF_PARTIAL_APP_IN_LET

#include "small_vector.h"
#include <atomic>
#include <functional>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
struct Positive;

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
};

struct Positive {
  // TYPES
  struct XI {
    std::shared_ptr<Positive> a0;
  };

  struct XO {
    std::shared_ptr<Positive> a0;
  };

  struct XH {};

  using variant_t = std::variant<XI, XO, XH>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Positive() {}

  explicit Positive(XI _v) : v_(std::move(_v)) {}

  explicit Positive(XO _v) : v_(std::move(_v)) {}

  explicit Positive(XH _v) : v_(_v) {}

  static Positive xi(Positive a0) {
    return Positive(XI{std::make_shared<Positive>(std::move(a0))});
  }

  static Positive xo(Positive a0) {
    return Positive(XO{std::make_shared<Positive>(std::move(a0))});
  }

  static Positive xh() { return Positive(XH{}); }

  // MANIPULATORS
  ~Positive() {
    crane::small_vector<std::shared_ptr<Positive>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<XI>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<XO>(&_v)) {
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

  Positive(const Positive &) = default;
  Positive &operator=(const Positive &) = default;
  Positive(Positive &&) noexcept = default;
  Positive &operator=(Positive &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Pos {
  static Positive succ(const Positive &x);

  template <typename T1>
  static T1 peano_rect(T1 a,
                       std::type_identity_t<std::function<T1(Positive, T1)>> f,
                       const Positive &p) {
    std::function<T1(Positive)> f2 = peano_rect<T1>(
        f(Positive::xh(), a), [=](Positive p0, const T1 &x) mutable {
          return f(succ(Positive::xo(p0)), f(Positive::xo(p0), x));
        });
    if (std::holds_alternative<typename Positive::XI>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XI>(p.v());
      return f(Positive::xo(*a0), f2(*a0));
    } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XO>(p.v());
      return f2(*a0);
    } else {
      return a;
    }
  }
};

struct SelfPartialAppInLet {
  static inline const Nat run = Pos::peano_rect(
      Nat::o(), [](const Positive &, Nat n) { return Nat::s(n); },
      Positive::xi(Positive::xo(Positive::xh())));
};

#endif // INCLUDED_SELF_PARTIAL_APP_IN_LET
