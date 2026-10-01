#ifndef INCLUDED_CONCEPT_MENTIONS_ALIAS_AND_MODULE_TYPE
#define INCLUDED_CONCEPT_MENTIONS_ALIAS_AND_MODULE_TYPE

#include "crane_fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

enum class Bool0;
struct Nat;
struct showNat;

/// Named qualified by the concept, so a forward declaration will not do.
struct Coll {
  template <typename A> struct bag {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      std::shared_ptr<bag<A>> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    bag() {}

    explicit bag(Nil _v) : v_(_v) {}

    explicit bag(Cons _v) : v_(std::move(_v)) {}

    template <typename _U>
    bag(const bag<_U> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename bag<_U>::Nil>(_other.v())) {
              return Nil{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename bag<_U>::Cons>(_other.v());
              return Cons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const _U &>) {
                      return crane_convert<A>(a0);
                    } else {
                      throw std::logic_error(
                          "unreachable: inactive constructor field at this "
                          "instantiation");
                    }
                  }(),
                  (a1 ? std::make_shared<bag<A>>(crane_convert<bag<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

    static bag<A> nil() { return bag<A>(Nil{}); }

    static bag<A> cons(A a0, bag<A> a1) {
      return bag<A>(
          Cons{std::move(a0), std::make_shared<bag<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~bag() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<bag<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<bag<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    bag(const bag &) = default;
    bag &operator=(const bag &) = default;
    bag(bag &&) noexcept = default;
    bag &operator=(bag &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };
};

/// An alias, which is the kind of declaration C++ cannot forward-declare.
using Name = Coll::bag<Nat>;
template <typename I, typename A>
concept Show = requires {
  { I::show(std::declval<A>()) } -> std::convertible_to<Name>;
  { I::tag(std::declval<A>()) } -> std::convertible_to<Coll::bag<Bool0>>;
};
enum class Bool0 { TRUE_, FALSE_ };

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

struct showNat {
  static Name show(Nat n) {
    return Coll::template bag<Nat>::cons(std::move(n),
                                         Coll::template bag<Nat>::nil());
  }

  static Coll::bag<Bool0> tag(Nat) {
    return Coll::template bag<Bool0>::cons(Bool0::TRUE_,
                                           Coll::template bag<Bool0>::nil());
  }
};

static_assert(Show<showNat, Nat>);

struct ConceptMentionsAliasAndModuleType {
  static inline const Name run =
      showNat::show(Nat::s(Nat::s(Nat::s(Nat::o()))));
};

#endif // INCLUDED_CONCEPT_MENTIONS_ALIAS_AND_MODULE_TYPE
