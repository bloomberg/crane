#ifndef INCLUDED_TEMPLATE_MERGE_OUTLINED_MEMBER
#define INCLUDED_TEMPLATE_MERGE_OUTLINED_MEMBER

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct Box;

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
  static bool eqb(const Nat &n, const Nat &m);
};

template <typename A> struct Box {
  // TYPES
  struct Bx {
    A a0;
  };

  struct Bnil {};

  using variant_t = std::variant<Bx, Bnil>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Box() {}

  explicit Box(Bx _v) : v_(std::move(_v)) {}

  explicit Box(Bnil _v) : v_(_v) {}

  template <typename _U> Box(const Box<_U> &_other) {
    if (std::holds_alternative<typename Box<_U>::Bx>(_other.v())) {
      const auto &[a0] = std::get<typename Box<_U>::Bx>(_other.v());
      this->v_ = Bx{[&]() -> A {
        if constexpr (crane_convertible<A, const _U &>) {
          return crane_convert<A>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    } else {
      this->v_ = Bnil{};
    }
  }

  static Box<A> bx(A a0) { return Box<A>(Bx{std::move(a0)}); }

  static Box<A> bnil() { return Box<A>(Bnil{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat size() const;

  Nat raw_size() const {
    if (std::holds_alternative<typename Box<A>::Bx>(this->v())) {
      return Nat::s(Nat::o());
    } else {
      return Nat::o();
    }
  }
};

struct Tally {
  struct boxed {
    Box<Nat> unbox;
  };

  static Nat bump(Nat n);
};

Box<Nat> roundtrip(Box<Nat> x);
bool sz_is(const Box<Nat> &b, const Nat &n);
Box<Nat> round(const Box<Nat> &x0_);

template <typename A> Nat Box<A>::size() const {
  return Tally::bump(this->raw_size());
}

#endif // INCLUDED_TEMPLATE_MERGE_OUTLINED_MEMBER
