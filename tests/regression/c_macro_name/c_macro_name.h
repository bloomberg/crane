#ifndef INCLUDED_C_MACRO_NAME
#define INCLUDED_C_MACRO_NAME

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

  static Request Alloca_(Nat size, Nat align, bool zeroed) {
    return Request(Alloca{std::move(size), std::move(align), zeroed});
  }

  static Request free(Nat addr) { return Request(Free{std::move(addr)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct CMacroName {
  static inline const Request example = Request::Alloca_(
      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))))),
      Nat::s(Nat::o()), true);
};

#endif // INCLUDED_C_MACRO_NAME
