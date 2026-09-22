#ifndef INCLUDED_METHOD_BODY_NAMES_LATER_STRUCT
#define INCLUDED_METHOD_BODY_NAMES_LATER_STRUCT

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
enum class Comparison;
struct Zed;

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
enum class Comparison { EQ, LT, GT };

struct PeanoNat {
  static Comparison compare(const Nat &n, const Nat &m);
};

struct Zed {
  // TYPES
  struct Zp {
    Nat a0;
  };

  struct Zn {
    Nat a0;
  };

  using variant_t = std::variant<Zp, Zn>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Zed() {}

  explicit Zed(Zp _v) : v_(std::move(_v)) {}

  explicit Zed(Zn _v) : v_(std::move(_v)) {}

  static Zed zp(Nat a0) { return Zed(Zp{std::move(a0)}); }

  static Zed zn(Nat a0) { return Zed(Zn{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool le_dec(const Zed &y) const;
  Comparison raw_cmp(const Zed &y) const;
};

struct Arith {
  static Zed roundtrip(Zed x);
  static Comparison norm(Comparison c);
};

bool le(const Zed &x0_, const Zed &x1_);
Zed round(const Zed &x0_);

inline bool Zed::le_dec(const Zed &y) const {
  switch (Arith::norm(this->raw_cmp(y))) {
  case Comparison::GT: {
    return false;
  }
  default: {
    return true;
  }
  }
}

inline Comparison Zed::raw_cmp(const Zed &y) const {
  if (std::holds_alternative<typename Zed::Zp>(this->v())) {
    const auto &[a0] = std::get<typename Zed::Zp>(this->v());
    if (std::holds_alternative<typename Zed::Zp>(y.v())) {
      const auto &[a00] = std::get<typename Zed::Zp>(y.v());
      return PeanoNat::compare(a0, a00);
    } else {
      return Comparison::GT;
    }
  } else {
    const auto &[a0] = std::get<typename Zed::Zn>(this->v());
    if (std::holds_alternative<typename Zed::Zp>(y.v())) {
      return Comparison::LT;
    } else {
      const auto &[a00] = std::get<typename Zed::Zn>(y.v());
      return PeanoNat::compare(a00, a0);
    }
  }
}

#endif // INCLUDED_METHOD_BODY_NAMES_LATER_STRUCT
