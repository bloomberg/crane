#ifndef INCLUDED_CLASS_ARG_IN_METHOD
#define INCLUDED_CLASS_ARG_IN_METHOD

#include "crane_fn.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
struct Memory_bit;
template <typename I>
concept Params = requires {
  { I::width() } -> std::convertible_to<Nat>;
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

  Nat add(Nat m) const {
    std::shared_ptr<Nat> _head{};
    std::shared_ptr<Nat> *_write = &_head;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        *_write = std::make_shared<Nat>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = std::make_shared<Nat>(typename Nat::S(nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename Nat::S>((*_write)->v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_head);
  }
};

struct Memory_bit {
  // TYPES
  struct Byte {
    Nat b;
  };

  struct Ptr {
    Nat p;
  };

  using variant_t = std::variant<Byte, Ptr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Memory_bit() {}

  explicit Memory_bit(Byte _v) : v_(std::move(_v)) {}

  explicit Memory_bit(Ptr _v) : v_(std::move(_v)) {}

  static Memory_bit byte(Nat b) { return Memory_bit(Byte{std::move(b)}); }

  static Memory_bit ptr(Nat p) { return Memory_bit(Ptr{std::move(p)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <Params _tcI0> Nat show_memory_bit() const {
    if (std::holds_alternative<typename Memory_bit::Byte>(this->v())) {
      const auto &[b0] = std::get<typename Memory_bit::Byte>(this->v());
      return b0.add(_tcI0::width());
    } else {
      const auto &[p] = std::get<typename Memory_bit::Ptr>(this->v());
      return p;
    }
  }
};

struct ClassArgInMethod {
  template <Params _tcI0> static Nat use(const Memory_bit &x0_) {
    return x0_.template show_memory_bit<_tcI0>();
  }
};

#endif // INCLUDED_CLASS_ARG_IN_METHOD
