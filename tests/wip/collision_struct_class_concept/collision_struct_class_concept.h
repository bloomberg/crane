#ifndef INCLUDED_COLLISION_STRUCT_CLASS_CONCEPT
#define INCLUDED_COLLISION_STRUCT_CLASS_CONCEPT

#include <atomic>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
struct Ident;

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

struct Ident {
  // TYPES
  struct Global {
    Nat n;
  };

  struct Local {
    Nat n;
  };

  using variant_t = std::variant<Global, Local>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Ident() {}

  explicit Ident(Global _v) : v_(std::move(_v)) {}

  explicit Ident(Local _v) : v_(std::move(_v)) {}

  static Ident global(Nat n) { return Ident(Global{std::move(n)}); }

  static Ident local(Nat n) { return Ident(Local{std::move(n)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct PeanoNat {
  static bool eqb(const Nat &n, const Nat &m);
};

struct AstLike {
  struct keyed_nat {
    static Nat key_of(Nat n) { return n; }
  };

  static_assert(Keyed<keyed_nat, Nat>);

  template <typename _tcI0, typename T1>
    requires Keyed<_tcI0, T1>
  static bool same(const T1 &x, const T1 &y) {
    return AstLike::eq(_tcI0::key_of(x), _tcI0::key_of(y));
  }

  static bool eq(const Nat &x0_, const Nat &x1_);
};

Ident to_ident(const Nat &n);
const bool check = AstLike::template same<AstLike::keyed_nat, Nat>(
    Nat::s(Nat::s(Nat::s(Nat::o()))), Nat::s(Nat::s(Nat::s(Nat::o()))));

#endif // INCLUDED_COLLISION_STRUCT_CLASS_CONCEPT
