#ifndef INCLUDED_CTOR_CASE_COLLISION
#define INCLUDED_CTOR_CASE_COLLISION

#include "small_vector.h"
#include <atomic>
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

struct CtorCaseCollision {
  /// Two constructors of the same inductive that differ only in the case of
  /// their first letter both mangle to the C++ identifier Foo:
  ///
  /// using variant_t = std::variant<Foo, Foo>;
  ///
  /// error: redefinition of 'Foo'
  /// error: constructor cannot be redeclared
  struct c {
    // TYPES
    struct Foo {
      Nat a0;
    };

    struct Foo {
      bool a0;
    };

    using variant_t = std::variant<Foo, Foo>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    c() {}

    explicit c(Foo _v) : v_(std::move(_v)) {}

    explicit c(Foo _v) : v_(std::move(_v)) {}

    static c foo(Nat a0) { return c(Foo{std::move(a0)}); }

    static c foo(bool a0) { return c(Foo{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  static Nat get(const c &x);
};

#endif // INCLUDED_CTOR_CASE_COLLISION
