#ifndef INCLUDED_COLLISION_WRAPPER_DROPS_CHILD_MODULE
#define INCLUDED_COLLISION_WRAPPER_DROPS_CHILD_MODULE

#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
struct Ident;
template <typename M>
concept MiniTyp = requires {
  typename M::t;
  {
    M::eq_dec(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<bool>;
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

  static ::Ident global(Nat n) { return ::Ident(Global{std::move(n)}); }

  static ::Ident local(Nat n) { return ::Ident(Local{std::move(n)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct PeanoNat {
  static bool eqb(const Nat &n, const Nat &m);
};

struct AstLike {
  struct Raw_id {
    // TYPES
    struct Name {
      Nat n;
    };

    struct Anon {
      Nat n;
    };

    using variant_t = std::variant<Name, Anon>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Raw_id() {}

    explicit Raw_id(Name _v) : v_(std::move(_v)) {}

    explicit Raw_id(Anon _v) : v_(std::move(_v)) {}

    static Raw_id name(Nat n) { return Raw_id(Name{std::move(n)}); }

    static Raw_id anon(Nat n) { return Raw_id(Anon{std::move(n)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    Nat tag() const {
      if (std::holds_alternative<typename AstLike::Raw_id::Name>(this->v())) {
        const auto &[n0] = std::get<typename AstLike::Raw_id::Name>(this->v());
        return n0;
      } else {
        const auto &[n0] = std::get<typename AstLike::Raw_id::Anon>(this->v());
        return n0;
      }
    }
  };

  template <MiniTyp T> struct Make_UDT {
    using t = typename T::t;

    static bool eq_dec(t x0_, t x1_) {
      return T::eq_dec(std::move(x0_), std::move(x1_));
    }
  };

  struct IdentDec {
    using t = Nat;
    static bool eq_dec(const Nat &x0_, const Nat &x1_);
  };

  struct RawIDOrdDec {
    using t = Nat;
    static bool eq_dec(const Nat &x0_, const Nat &x1_);
  };

  using Ident = AstLike::Make_UDT<AstLike::IdentDec>;
  using RawIDOrd = AstLike::Make_UDT<AstLike::RawIDOrdDec>;

  struct Ord {
    using t = AstLike::Raw_id;
    static bool cmp(const AstLike::Raw_id &x, const AstLike::Raw_id &y);
    static bool compare(const AstLike::Raw_id &x, const AstLike::Raw_id &y);
  };
};

::Ident to_ident(const AstLike::Raw_id &k);
std::pair<::Ident, std::pair<std::pair<bool, bool>, bool>>
both(const AstLike::Raw_id &k);

#endif // INCLUDED_COLLISION_WRAPPER_DROPS_CHILD_MODULE
