#ifndef INCLUDED_C_MACRO_NAME
#define INCLUDED_C_MACRO_NAME

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
struct Request;

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

struct Request {
  // TYPES
  struct Alloca {
    Nat size;
    Nat align;
    bool zeroed;
  };

  struct Free {
    Nat addr;
  };

  using variant_t = std::variant<Alloca, Free>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Request() {}

  explicit Request(Alloca _v) : v_(std::move(_v)) {}

  explicit Request(Free _v) : v_(std::move(_v)) {}

  static Request alloca(Nat size, Nat align, bool zeroed) {
    return Request(Alloca{std::move(size), std::move(align), zeroed});
  }

  static Request free(Nat addr) { return Request(Free{std::move(addr)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct CMacroName {
  static inline const Request example = Request::alloca(
      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))))),
      Nat::s(Nat::o()), true);
};

#endif // INCLUDED_C_MACRO_NAME
