#ifndef INCLUDED_MODTYPE_ALIAS_EMITTED_BEFORE_ORIGINAL
#define INCLUDED_MODTYPE_ALIAS_EMITTED_BEFORE_ORIGINAL

#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <memory>
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

struct PeanoNat {
  static bool eq_dec(const Nat &n, const Nat &m);
};

template <typename M>
concept DecOrig = requires {
  typename M::t;
  {
    M::eq_dec(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<bool>;
};
const Nat tag =
    Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))));
template <typename M>
concept Dec = DecOrig<M>;

template <Dec X> struct Make {
  static bool same(typename X::t a, typename X::t b) {
    if (X::eq_dec(a, b)) {
      return true;
    } else {
      return false;
    }
  }
};

struct NatDec {
  using t = Nat;
  static bool eq_dec(t x0_, t x1_);
};

using MN = Make<NatDec>;
bool go(const Nat &x0_, const Nat &x1_);
const Nat tag2 = tag;

#endif // INCLUDED_MODTYPE_ALIAS_EMITTED_BEFORE_ORIGINAL
