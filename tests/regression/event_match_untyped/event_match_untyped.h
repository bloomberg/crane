#ifndef INCLUDED_EVENT_MATCH_UNTYPED
#define INCLUDED_EVENT_MATCH_UNTYPED

#include <atomic>
#include <crane_itree.h>
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
};

struct EventMatchUntyped {
  struct IOE {
    // TYPES
    struct Rd {};

    struct Wr {
      Nat a0;
    };

    using variant_t = std::variant<Rd, Wr>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    IOE() {}

    explicit IOE(Rd _v) : v_(_v) {}

    explicit IOE(Wr _v) : v_(std::move(_v)) {}

    static IOE rd() { return IOE(Rd{}); }

    static IOE wr(Nat a0) { return IOE(Wr{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  /// The event is matched in the very branch that binds it, so nothing
  /// downstream says what type it has.
  static Nat weight(const std::shared_ptr<ITree<Nat>> &t);
};

#endif // INCLUDED_EVENT_MATCH_UNTYPED
