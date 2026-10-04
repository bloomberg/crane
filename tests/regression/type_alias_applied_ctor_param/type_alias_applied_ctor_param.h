#ifndef INCLUDED_TYPE_ALIAS_APPLIED_CTOR_PARAM
#define INCLUDED_TYPE_ALIAS_APPLIED_CTOR_PARAM

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <memory>
#include <optional>
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

struct TypeAliasAppliedCtorParam {
  /// A type-level definition that applies its own type-constructor argument
  /// becomes a C++ alias template whose first parameter is a plain typename
  /// but is then used as a template:
  ///
  /// template <typename f, typename a> using ap = f<a>;
  /// ...
  /// ap<F<std::any>, Nat> a0;
  ///
  /// error: expected ';' after alias declaration
  /// error: expected '>'
  ///
  /// f needs to be template <typename> class f, and the use site must pass
  /// F, not F<std::any>.
  template <typename f, typename a> using ap = crane::rebind_t<f, a>;

  template <typename F> struct holder {
    // DATA
    ap<F, Nat> a0;

    // ACCESSORS
    holder<F> clone() const { return {a0}; }

    template <typename CraneU> operator holder<CraneU>() const {
      return {crane_convert<ap<CraneU, Nat>>(a0)};
    }

    // CREATORS
    static holder<F> hold(ap<F, Nat> a0) { return {std::move(a0)}; }
  };

  static inline const holder<std::optional<crane::obj>> mk =
      holder<std::optional<crane::obj>>::hold(
          std::make_optional<Nat>(Nat::s(Nat::o())));

  static std::optional<Nat> get(const holder<std::optional<crane::obj>> &h);
};

#endif // INCLUDED_TYPE_ALIAS_APPLIED_CTOR_PARAM
