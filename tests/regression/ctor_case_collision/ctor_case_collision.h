#ifndef INCLUDED_CTOR_CASE_COLLISION
#define INCLUDED_CTOR_CASE_COLLISION

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

struct CtorCaseCollision {
  /// Constructors are emitted as PascalCase nested structs, so two constructors
  /// of the same inductive that differ only in the case of their first letter
  /// compete for one C++ name.  Sibling reservation is done on that spelling,
  /// so the second one is renamed:
  ///
  /// using variant_t = std::variant<Foo, Foo0>;
  struct c {
    // TYPES
    struct Foo {
      Nat a0;
    };

    struct Foo0 {
      bool a0;
    };

    using variant_t = std::variant<Foo, Foo0>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    c() {}

    explicit c(Foo _v) : v_(std::move(_v)) {}

    explicit c(Foo0 _v) : v_(std::move(_v)) {}

    static c foo(Nat a0) { return c(Foo{std::move(a0)}); }

    static c foo0(bool a0) { return c(Foo0{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  static Nat get(const c &x);
};

#endif // INCLUDED_CTOR_CASE_COLLISION
